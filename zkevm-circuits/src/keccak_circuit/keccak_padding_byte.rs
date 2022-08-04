use crate::{
    evm_circuit::{
        util::{constraint_builder::BaseConstraintBuilder},
    },
    util::Expr,
};

use eth_types::Field;
use gadgets::util::not;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn,
    },
    poly::Rotation,
};
use std::{env::var, marker::PhantomData, vec};

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const KECCAK_RATE: usize = 1088;

const KECCAK_WIDTH_IN_BYTES: usize = KECCAK_WIDTH / 8;
const KECCAK_RATE_IN_BYTES: usize = KECCAK_RATE / 8;

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

// [s_flags]    0 (data) 0 (data)  (pad) 1  (pad) 1  (pad) 1
// [d_bytes]       79      106      128        0       1      [0]*CAPACITY//8
// [d_lens]      base+1   base+2   base+2   base+2   base+2
// [rlc]

#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct PaddingCombinationsConfig<F> {
    pub byte_range_col: TableColumn,
    pub s_flag_col: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field> PaddingCombinationsConfig<F> {

    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            byte_range_col: meta.lookup_table_column(),
            s_flag_col: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        const K: u64 = 256;
        layouter.assign_table(
            // The table will estrict padding flags to {0,1} and data/padding bytes to [0, 255].
            // Only particular combinations are allowed, i.e. data sections are restricted to (0, [0, 255]), 
            // and padding sections to {(1, 0), (1, 128), (1, 129), (1, 1)}.
            || "byte-s_flag combination table",
            |mut table| {
                for i in 0..=K {
                    table.assign_cell(|| "byte_range_col_[i=0:K-1]", self.byte_range_col, i as usize, || Ok(F::from(i)))?;
                    table.assign_cell(|| "s_flag_col_[i=0:K-1]", self.s_flag_col, i as usize, || Ok(F::from(0)))?;
                }
                
                // byte = 0, s_flag = 1, the middle of the padding case
                table.assign_cell(|| "byte_range_col_[i=K]", self.byte_range_col, (K) as usize, || Ok(F::from(0)))?;
                table.assign_cell(|| "s_flag_col_[i=K]", self.s_flag_col, (K) as usize, || Ok(F::from(1)))?;

                // byte = 128, s_flag = 1, the beginning of the padding separate from end case
                table.assign_cell(|| "byte_range_col_[i=K+1]", self.byte_range_col, (K + 1) as usize, || Ok(F::from(128)))?;
                table.assign_cell(|| "s_flag_col_[i=K+1]", self.s_flag_col, (K + 1) as usize, || Ok(F::from(1)))?;
            
                // byte = 129, s_flag = 1, the beginning of the padding same as end case
                table.assign_cell(|| "byte_range_col_[i=K+1]", self.byte_range_col, (K + 2) as usize, || Ok(F::from(129)))?;
                table.assign_cell(|| "s_flag_col_[i=K+1]", self.s_flag_col, (K + 2) as usize, || Ok(F::from(1)))?;

                // byte = 1, s_flag = 1, the end of the padding separate from beginning case
                table.assign_cell(|| "byte_range_col_[i=K+1]", self.byte_range_col, (K + 3) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "s_flag_col_[i=K+1]", self.s_flag_col, (K + 3) as usize, || Ok(F::from(1)))?;

                Ok(())
            },
        )
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 

#[derive(Clone, Debug)]
#[allow(missing_docs)]
pub struct KeccakPaddingConfig<F> {
    q_enable: Selector,
    q_end: Column<Advice>,
    d_bytes: [Column<Advice>; KECCAK_WIDTH_IN_BYTES],
    d_lens: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    d_rlcs: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    s_flags: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    randomness: Column<Advice>,
    _marker: PhantomData<F>,
    padding_combinations_table: PaddingCombinationsConfig<F>,
}

impl<F: Field> KeccakPaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let randomness = meta.advice_column();        
        let q_enable = meta.selector();
        let q_end = meta.advice_column();

        let padding_combinations_table = PaddingCombinationsConfig::<F>::configure(meta);

        let d_bytes = [(); KECCAK_WIDTH_IN_BYTES].map(|_| meta.advice_column());
        let d_lens = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let d_rlcs = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let s_flags = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        
        // Check that (padding flag, data/padding byte) combinations are restricted to the combinations in padding_combinations_table.        
        // The table will estrict padding flags to {0,1} and data/padding bytes to [0, 255].
        // Only particular combinations are allowed, i.e. data sections are restricted to (0, [0, 255]), 
        // and padding sections to {(1, 0), (1, 128), (1, 129), (1, 1)}.
        for i in 0..s_flags.len() {
            meta.lookup("Check allowed data/padding/flag combinations", |meta| {
                // let q_enable = meta.query_selector(q_enable);
                vec![
                    (meta.query_advice(d_bytes[i], Rotation::cur()), padding_combinations_table.byte_range_col),
                    (meta.query_advice(s_flags[i], Rotation::cur()), padding_combinations_table.s_flag_col),
                ]
            });
        };

        meta.create_gate("Check inter-cell relationships", |virt_cells| {
            let mut cb = BaseConstraintBuilder::new(5);
            
            let q_end = virt_cells.query_advice(q_end, Rotation::cur());
            let d_last_byte = virt_cells.query_advice(d_bytes[s_flags.len() - 1], Rotation::cur());

            let s_last = virt_cells.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
            let s_last_prev = virt_cells.query_advice(s_flags[s_flags.len() - 2], Rotation::cur());
            
            let s_last_separate = s_last.clone() * s_last_prev.clone(); 
            let s_last_same = s_last.clone() * not::expr(s_last_prev.clone());

            // Ensure that if q_end is true (last data or padding block to be sent to the hash function), 
            // the last padding flag is 1 and zero otherwise.)
            // Everything cascades from this condition.
            cb.require_equal("s_last == q_end", s_last.clone(), q_end.clone());

            // Based on the value of s_last_separate, which is 1 if the last two padding flags are 1, 
            // constrain the last data+padding byte to 1. 
            cb.condition(s_last_separate.clone(), |cb| {
                cb.require_equal("Check d_bytes padding start-end separate", d_last_byte.clone(), 1u64.expr());
            });

            // Based on the value of s_last_same, which is 1 if the last two padding flags are (0, 1), 
            // constrain the last data+padding byte to 129. 
            cb.condition(s_last_same.clone(), |cb| {
                cb.require_equal("Check d_bytes padding start-end the same", d_last_byte.clone(), 129u64.expr());
            });

            // This is where most of the constraints are effectuated for the padding flags and data/padding bytes. 
            for i in 0..s_flags.len() {
                let d_bytes_i = virt_cells.query_advice(d_bytes[i], Rotation::cur());
                let s_i = virt_cells.query_advice(s_flags[i], Rotation::cur());
            
                let mut s_i_1 = 0u64.expr();
                if i > 0 {
                    s_i_1 = virt_cells.query_advice(s_flags[i - 1], Rotation::cur());
                }
                let s_padding_step = s_i.clone() - s_i_1.clone();

                // First, we enforce monotonicity to the padding flags. Combined with the table restrictions, 
                // this ensures that padding flags are [0]*[1]*, zeroes followed by ones.
                cb.require_boolean("Check that padding flags are monotonically non-decreasing.", s_padding_step.clone());
                
                // Based on the value of s_last_same and s_last_separate, we go through each element and 
                // detect if there is a step function change in the padding flags, and constrain the respective
                // byte to 129 or 128 respectively. 
                cb.condition(s_padding_step.clone() * s_last_separate.clone(), |cb| {
                    cb.require_equal("Check d_bytes padding start", d_bytes_i.clone(), 128u64.expr());
                });

                cb.condition(s_padding_step.clone() * s_last_same.clone(), |cb| {
                    cb.require_equal("Check d_bytes padding start", d_bytes_i.clone(), 129u64.expr());
                });
                
                // Further if there is no step function change and the padding flag is 1, then we are in the intermediate
                // regions of the padding, and therefore need to constrain the respective byte to zero (except last element). 
                if i < (s_flags.len() - 1) {
                    cb.condition(not::expr(s_padding_step.clone()) * s_i.clone(), |cb| {
                        cb.require_equal("Check d_bytes padding intermediate", d_bytes_i.clone(), 0u64.expr());
                    });
                }
            }    
            cb.gate(virt_cells.query_selector(q_enable))
        });

        meta.create_gate("Check len and rlc inputs", |virt_cells| {
            let mut cb = BaseConstraintBuilder::new(5);

            // Check that d_len elements are increasing by one if they do not correspond to padding 
            for i in 1..s_flags.len() {
                let s_i = virt_cells.query_advice(s_flags[i], Rotation::cur());
                let d_len_i = virt_cells.query_advice(d_lens[i], Rotation::cur());
                let d_len_i_1 = virt_cells.query_advice(d_lens[i - 1], Rotation::cur());                
                cb.require_equal("d_len[i] = d_len[i-1] + !s_i", d_len_i.clone(), d_len_i_1.clone() + not::expr(s_i.clone()));
            }

            // Check that rlc elements are changing properly if they do not correspond to padding 
            for i in 1..s_flags.len() {
                let d_bytes_i = virt_cells.query_advice(d_bytes[i], Rotation::cur());
                let s_i = virt_cells.query_advice(s_flags[i], Rotation::cur());
                let rlc_i = virt_cells.query_advice(d_rlcs[i], Rotation::cur());
                let rlc_i_1 = virt_cells.query_advice(d_rlcs[i - 1], Rotation::cur());
                let r = virt_cells.query_advice(randomness, Rotation::cur());
                cb.require_equal("rlc[i] = rlc[i-1]*r if s == 0 else rlc[i]", rlc_i.clone(), 
                s_i.clone() * rlc_i.clone() + not::expr(s_i.clone()) * (rlc_i_1.clone() * r.clone() + d_bytes_i.clone()));
            }

            cb.gate(virt_cells.query_selector(q_enable))
        });

        KeccakPaddingConfig {
            q_enable,
            q_end,
            d_bytes,
            d_lens,
            d_rlcs,
            s_flags,
            randomness,
            _marker: PhantomData,
            padding_combinations_table, 
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        keccak_padding_row: &KeccakPaddingRow<F>,
        randomness: F,
    ) -> Result<(), Error> {
        self.padding_combinations_table.load(&mut layouter)?;
        layouter.assign_region(
            || "assign keccak padded data",
            |mut region| {
                self.set_row(
                    &mut region,
                    0,
                    keccak_padding_row.q_end,
                    keccak_padding_row.d_bytes,
                    keccak_padding_row.d_lens,
                    keccak_padding_row.d_rlcs,
                    keccak_padding_row.s_flags,
                    randomness,
                )?;
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        q_end: u64,
        d_bytes: [u8; KECCAK_WIDTH_IN_BYTES],
        d_lens: [u32; KECCAK_RATE_IN_BYTES],
        d_rlcs: [F; KECCAK_RATE_IN_BYTES],
        s_flags: [bool; KECCAK_RATE_IN_BYTES],
        randomness: F,
    ) -> Result<(), Error> {
        self.q_enable.enable(region, offset)?;

        // Input bytes w/ padding
        for (idx, (byte, column)) in d_bytes.iter().zip(self.d_bytes.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data byte {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*byte as u64)),
            )?;
        }

        for (idx, (s_flag, column)) in s_flags.iter().zip(self.s_flags.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data select flag {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*s_flag as u64)),
            )?;
        }

        for (idx, (d_len, column)) in d_lens.iter().zip(self.d_lens.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data len {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*d_len as u64)),
            )?;
        }

        for (idx, (d_rlc, column)) in d_rlcs.iter().zip(self.d_rlcs.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data rlc {} {}", idx, offset),
                *column,
                offset,
                || Ok(*d_rlc),
            )?;
        }

        region.assign_advice(
            || format!("assign q_end{}", offset),
            self.q_end,
            offset,
            || Ok(F::from(q_end)),
        )?;

        region.assign_advice(
            || format!("assign randomness{}", offset),
            self.randomness,
            offset,
            || Ok(randomness),
        )?;

        Ok(())
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 

pub(crate) struct KeccakPaddingRow<F: Field> {
    pub(crate) randomness: F,
    pub(crate) q_end: u64,
    pub(crate) acc_len: u32,
    pub(crate) acc_rlc: F,
    pub(crate) d_bytes: [u8; KECCAK_WIDTH_IN_BYTES],
    pub(crate) d_lens: [u32; KECCAK_RATE_IN_BYTES],
    pub(crate) d_rlcs: [F; KECCAK_RATE_IN_BYTES],
    pub(crate) s_flags: [bool; KECCAK_RATE_IN_BYTES],
}

impl<F: Field> KeccakPaddingRow<F> {

    fn clone(&self) -> KeccakPaddingRow<F> {
        KeccakPaddingRow::<F> {
            s_flags:  self.s_flags,
            d_lens:  self.d_lens,
            d_bytes: self.d_bytes,
            d_rlcs: self.d_rlcs,
            q_end: self.q_end,
            randomness: self.randomness,
            acc_len: self.acc_len,
            acc_rlc: self.acc_rlc,
        }
    }

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 

#[derive(Default)]
#[allow(missing_docs)]
pub struct KeccakPaddingCircuit<F: Field> {
    inputs: Vec<KeccakPaddingRow<F>>,
    size: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> KeccakPaddingCircuit<F> {
    fn r() -> F {
        F::from(123456)
    }
}

impl<F: Field> Circuit<F> for KeccakPaddingCircuit<F> {
    type Config = KeccakPaddingConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        KeccakPaddingConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.assign(
            layouter,
            self.size,
            &self.inputs[0],
            KeccakPaddingCircuit::r(),
        )?;
        Ok(())
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};
    use rand::{thread_rng, Fill};

    fn verify<F: Field>(k: u32, inputs: Vec<KeccakPaddingRow<F>>, success: bool) {
        let circuit = KeccakPaddingCircuit::<F> {
            inputs,
            size: 2usize.pow(k),
            _marker: PhantomData,
        };
        let prover = MockProver::<F>::run(K, &circuit, vec![]).unwrap();


        let err = prover.verify();

        let print_failures = true;
        if err.is_err() && print_failures {
            for e in err.err().iter() {
                for s in e.iter() {
                    println!("{}", s);
                }
            }
        }
        let err = prover.verify();
        assert_eq!(err.is_ok(), success);
    }

    // [s_flags]    0 (data) 0 (data)  (pad) 1  (pad) 1  (pad) 1
    // [d_bytes]       79      106      128        0       1      [0]*CAPACITY//8
    // [d_lens]      base+1   base+2   base+2   base+2   base+2
    // [rlc] 

    fn generate_padding<F: Field>(data_len: u32) -> KeccakPaddingRow<F> {
        let data_len_offset = data_len % KECCAK_RATE_IN_BYTES as u32;        
        let data_len_offset_usize = data_len_offset as usize;
        let data_len_base = data_len - data_len_offset;

        let mut output = KeccakPaddingRow::<F> {
            s_flags: [false; KECCAK_RATE_IN_BYTES], 
            d_lens: [0; KECCAK_RATE_IN_BYTES], 
            d_bytes: [0; KECCAK_WIDTH_IN_BYTES],
            d_rlcs: [F::from(0u64); KECCAK_RATE_IN_BYTES],
            q_end: 1u64,
            randomness: KeccakPaddingCircuit::r(),
            acc_len: data_len_base,
            acc_rlc: F::one(),
        };

        let mut rng = thread_rng();
        output.d_bytes.try_fill(&mut rng).unwrap();
        for i in KECCAK_RATE_IN_BYTES..KECCAK_WIDTH_IN_BYTES {
            output.d_bytes[i] = 0u8;
        }

        output.s_flags[0] = data_len_offset_usize == 0;
        output.d_lens[0] = data_len_base + !output.s_flags[0] as u32;
        output.d_rlcs[0] = if output.s_flags[0] {
            output.acc_rlc
        } else {
            output.acc_rlc * output.randomness + F::from(output.d_bytes[0] as u64)
        };

        for i in 1 as usize..KECCAK_RATE_IN_BYTES {
            output.s_flags[i] = {
                if i < data_len_offset_usize {
                    false
                } else {
                    true
                }
            };
            output.d_lens[i] = output.d_lens[i - 1] + !output.s_flags[i] as u32; // add 1 if data
            output.d_rlcs[i] = if output.s_flags[i] {
                output.d_rlcs[i - 1]
            } else {
                output.d_rlcs[i - 1] * output.randomness + F::from(output.d_bytes[i] as u64)
            }
        }

        for i in data_len_offset_usize..KECCAK_RATE_IN_BYTES {
            output.d_bytes[i] = 0u8;
        }
        if data_len_offset_usize == (KECCAK_RATE_IN_BYTES - 1) {
            output.d_bytes[data_len_offset_usize] = 129;
        } else {
            output.d_bytes[data_len_offset_usize] = 128;
            output.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 1;
        }
       
        println!("{:?}", output.s_flags);
        println!("{:?}", output.d_lens);
        println!("{:?}", output.d_bytes);
        println!("Padding start: {:?}", output.d_bytes[data_len_offset_usize]);
        println!("Padding end: {:?}", output.d_bytes[KECCAK_RATE_IN_BYTES - 1]);
        println!("END");
        
        output
    }

    static K: u32 = 10;

    #[test]
    fn byte_keccak_len_0() {
        let input = generate_padding::<Fr>(0);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn byte_keccak_len_1() {
        let input = generate_padding::<Fr>(1);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn byte_keccak_len_135() {
        let input = generate_padding::<Fr>(135);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn byte_keccak_len_300() {
        let input = generate_padding::<Fr>(300);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn byte_keccak_invalid_padding_begin() {
        let mut input = generate_padding::<Fr>(11);
        verify::<Fr>(K, vec![input.clone()], true);

        // first padding byte is set to 0
        input.d_bytes[11] = 0u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn byte_keccak_invalid_padding_end() {
        let mut input = generate_padding::<Fr>(73);
        verify::<Fr>(K, vec![input.clone()], true);

        // last padding byte is set to 0
        input.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 0u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn byte_keccak_invalid_padding_mid() {
        let mut input = generate_padding::<Fr>(123);
        verify::<Fr>(K, vec![input.clone()], true);
        
        // nonzero padding in intermediate padding regions
        input.d_bytes[KECCAK_RATE_IN_BYTES - 2] = 1u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn byte_keccak_invalid_input_len() {
        let mut input = generate_padding::<Fr>(123);
        verify::<Fr>(K, vec![input.clone()], true);

        // wrong d_len
        input.d_lens[124] = 124;
        verify::<Fr>(K, vec![input], false);
    }
}
