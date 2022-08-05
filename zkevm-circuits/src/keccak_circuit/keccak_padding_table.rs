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


// [is_pads]          0 (data)   0 (data)  (pad) 1   (pad) 1  (pad) 1
// [is_pad_starts]    0 (data)   0 (data)  (pad) 1   (pad) 0  (pad) 0
// [is_pad_ends]      0 (data)   0 (data)  (pad) 0   (pad) 0  (pad) 1
// [d_bytes]             79         106       128       0        1      [0]*CAPACITY//8
// [d_lens]            base+1     base+2    base+2   base+2   base+2
// [rlc] 

#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct PaddingCombinationsConfig<F> {
    pub byte_col: TableColumn,
    pub is_padding_col: TableColumn,
    pub is_padding_start_col: TableColumn,
    pub is_padding_end_col: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field> PaddingCombinationsConfig<F> {

    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            byte_col: meta.lookup_table_column(),
            is_padding_col: meta.lookup_table_column(),
            is_padding_start_col: meta.lookup_table_column(),
            is_padding_end_col: meta.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        const K: u64 = 256;
        layouter.assign_table(
            // Only particular combinations are allowed, 
            // (is_padding_col, is_padding_start_col, is_padding_end_col, byte_col)
            // 0 | 0 | 0 | [all 256 possible byte values]
            // 1 | 1 | 0 | 128 // start-exclusive
            // 1 | 1 | 1 | 129 // start-end
            // 1 | 0 | 0 | 0 // mid
            // 1 | 0 | 1 | 1 // end-exclusive

            || "byte-is_pad-is_pad_start-is_pad_end combination table",
            |mut table| {
                for i in 0..K {
                    table.assign_cell(|| "byte_col_[i=0:K-1]", self.byte_col, i as usize, || Ok(F::from(i)))?;
                    table.assign_cell(|| "is_padding_col_[i=0:K-1]", self.is_padding_col, i as usize, || Ok(F::from(0)))?;
                    table.assign_cell(|| "is_padding_start_col_[i=0:K-1]", self.is_padding_start_col, i as usize, || Ok(F::from(0)))?;
                    table.assign_cell(|| "is_padding_end_col_[i=0:K-1]", self.is_padding_end_col, i as usize, || Ok(F::from(0)))?;
                }
                
                // the middle of the padding case
                table.assign_cell(|| "byte_col_[i=K]", self.byte_col, (K) as usize, || Ok(F::from(0)))?;
                table.assign_cell(|| "is_padding_col_[i=K]", self.is_padding_col, (K) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_start_col_[i=K]", self.is_padding_start_col, (K) as usize, || Ok(F::from(0)))?;
                table.assign_cell(|| "is_padding_end_col_[i=K]", self.is_padding_end_col, (K) as usize, || Ok(F::from(0)))?;

                // the beginning of the padding separate from end case
                table.assign_cell(|| "byte_col_[i=K+1]", self.byte_col, (K + 1) as usize, || Ok(F::from(128)))?;
                table.assign_cell(|| "is_padding_col_[i=K+1]", self.is_padding_col, (K + 1) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_start_col_[i=K+1]", self.is_padding_start_col, (K + 1) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_end_col_[i=K+1]", self.is_padding_end_col, (K + 1) as usize, || Ok(F::from(0)))?;

                // the beginning/end of the padding same as end/beginning case
                table.assign_cell(|| "byte_col_[i=K+2]", self.byte_col, (K + 2) as usize, || Ok(F::from(129)))?;
                table.assign_cell(|| "is_padding_col_[i=K+2]", self.is_padding_col, (K + 2) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_start_col_[i=K+2]", self.is_padding_start_col, (K + 2) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_end_col_[i=K+2]", self.is_padding_end_col, (K + 2) as usize, || Ok(F::from(1)))?;

                // the end of the padding separate from beginning case
                table.assign_cell(|| "byte_col_[i=K+3]", self.byte_col, (K + 3) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_col_[i=K+3]", self.is_padding_col, (K + 3) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_padding_start_col_[i=K+3]", self.is_padding_start_col, (K + 3) as usize, || Ok(F::from(0)))?;
                table.assign_cell(|| "is_padding_end_col_[i=K+3]", self.is_padding_end_col, (K + 3) as usize, || Ok(F::from(1)))?;

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
    is_pads: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    is_pad_starts: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    is_pad_ends: [Column<Advice>; KECCAK_RATE_IN_BYTES],
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
        let is_pads = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let is_pad_starts = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let is_pad_ends = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        
        // Check that (padding flag, data/padding byte) combinations are restricted to the combinations in padding_combinations_table.        
        // The table will estrict padding flags to {0,1} and data/padding bytes to [0, 255].
        // Only particular combinations are allowed, check PaddingCombinationsConfig load method comments.
        for i in 0..is_pads.len() {
            meta.lookup("Check allowed data/padding/flag combinations", |meta| {
                // let q_enable = meta.query_selector(q_enable);
                vec![
                    (meta.query_advice(d_bytes[i], Rotation::cur()), padding_combinations_table.byte_col),
                    (meta.query_advice(is_pads[i], Rotation::cur()), padding_combinations_table.is_padding_col),
                    (meta.query_advice(is_pad_starts[i], Rotation::cur()), padding_combinations_table.is_padding_start_col),
                    (meta.query_advice(is_pad_ends[i], Rotation::cur()), padding_combinations_table.is_padding_end_col),
                ]
            });
        };

        meta.create_gate("Check inter-cell relationships for data/padding/flag", |virt_cells| {
            let mut cb = BaseConstraintBuilder::new(5);
            
            // ?? IMPLEMENT THIS PART. SEEMS A BIT MORE COMPLICATED COMPARED TO keccak_padding_byte VERSION.

            // let q_end = virt_cells.query_advice(q_end, Rotation::cur());
            // let d_last_byte = virt_cells.query_advice(d_bytes[is_pads.len() - 1], Rotation::cur());

            // let is_pad_last = virt_cells.query_advice(is_pads[is_pads.len() - 1], Rotation::cur());
            // let is_pad_last_prev = virt_cells.query_advice(is_pads[is_pads.len() - 2], Rotation::cur());
            
            // let is_start_end_separate = is_pad_last.clone() * is_pad_last_prev.clone(); 
            // let is_start_end_same = is_pad_last.clone() * not::expr(is_pad_last_prev.clone());

            // // Ensure that if q_end is true (last data or padding block to be sent to the hash function), 
            // // the last padding flag is 1 and zero otherwise.)
            // // Everything cascades from this condition.
            // cb.require_equal("is_pad_last == q_end", is_pad_last.clone(), q_end.clone());

            // // Based on the value of is_start_end_separate, which is 1 if the last two padding flags are 1, 
            // // constrain the last data+padding byte to 1. 
            // cb.condition(is_start_end_separate.clone(), |cb| {
            //     cb.require_equal("Check d_bytes padding start-end separate", d_last_byte.clone(), 1u64.expr());
            // });

            // // Based on the value of is_start_end_same, which is 1 if the last two padding flags are (0, 1), 
            // // constrain the last data+padding byte to 129. 
            // cb.condition(is_start_end_same.clone(), |cb| {
            //     cb.require_equal("Check d_bytes padding start-end the same", d_last_byte.clone(), 129u64.expr());
            // });

            // // This is where most of the constraints are effectuated for the padding flags and data/padding bytes. 
            // for i in 0..is_pads.len() {
            //     let d_bytes_i = virt_cells.query_advice(d_bytes[i], Rotation::cur());
            //     let s_i = virt_cells.query_advice(is_pads[i], Rotation::cur());
            
            //     let mut s_i_1 = 0u64.expr();
            //     if i > 0 {
            //         s_i_1 = virt_cells.query_advice(is_pads[i - 1], Rotation::cur());
            //     }
            //     let s_padding_step = s_i.clone() - s_i_1.clone();

            //     // First, we enforce monotonicity to the padding flags. Combined with the table restrictions, 
            //     // this ensures that padding flags are [0]*[1]*, zeroes followed by ones.
            //     cb.require_boolean("Check that padding flags are monotonically non-decreasing.", s_padding_step.clone());
                
            //     // Based on the value of is_start_end_same and is_start_end_separate, we go through each element and 
            //     // detect if there is a step function change in the padding flags, and constrain the respective
            //     // byte to 129 or 128 respectively. 
            //     cb.condition(s_padding_step.clone() * is_start_end_separate.clone(), |cb| {
            //         cb.require_equal("Check d_bytes padding start", d_bytes_i.clone(), 128u64.expr());
            //     });

            //     cb.condition(s_padding_step.clone() * is_start_end_same.clone(), |cb| {
            //         cb.require_equal("Check d_bytes padding start", d_bytes_i.clone(), 129u64.expr());
            //     });
                
            //     // Further if there is no step function change and the padding flag is 1, then we are in the intermediate
            //     // regions of the padding, and therefore need to constrain the respective byte to zero (except last element). 
            //     if i < (is_pads.len() - 1) {
            //         cb.condition(not::expr(s_padding_step.clone()) * s_i.clone(), |cb| {
            //             cb.require_equal("Check d_bytes padding intermediate", d_bytes_i.clone(), 0u64.expr());
            //         });
            //     }
            // }    
            cb.gate(virt_cells.query_selector(q_enable))
        });

        meta.create_gate("Check len and rlc inputs", |virt_cells| {
            let mut cb = BaseConstraintBuilder::new(5);

            for i in 1..is_pads.len() {
                let s_i = virt_cells.query_advice(is_pads[i], Rotation::cur());
                let d_len_i = virt_cells.query_advice(d_lens[i], Rotation::cur());
                let d_len_i_1 = virt_cells.query_advice(d_lens[i - 1], Rotation::cur());                
                let d_bytes_i = virt_cells.query_advice(d_bytes[i], Rotation::cur());
                let rlc_i = virt_cells.query_advice(d_rlcs[i], Rotation::cur());
                let rlc_i_1 = virt_cells.query_advice(d_rlcs[i - 1], Rotation::cur());
                let r = virt_cells.query_advice(randomness, Rotation::cur());

                // Check that d_len elements are increasing by one if they do not correspond to padding 
                cb.require_equal("d_len[i] = d_len[i-1] + !s_i", d_len_i.clone(), d_len_i_1.clone() + not::expr(s_i.clone()));

                // Check that rlc elements are changing properly if they do not correspond to padding 
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
            is_pads,
            is_pad_starts,
            is_pad_ends,
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
                    keccak_padding_row.is_pads,
                    keccak_padding_row.is_pad_starts,
                    keccak_padding_row.is_pad_ends,
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
        is_pads: [bool; KECCAK_RATE_IN_BYTES],
        is_pad_starts: [bool; KECCAK_RATE_IN_BYTES],
        is_pad_ends: [bool; KECCAK_RATE_IN_BYTES],
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

        for (idx, (is_pad, column)) in is_pads.iter().zip(self.is_pads.iter()).enumerate() {
            region.assign_advice(
                || format!("assign pad flag {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*is_pad as u64)),
            )?;
        }

        for (idx, (is_pad_start, column)) in is_pad_starts.iter().zip(self.is_pad_starts.iter()).enumerate() {
            region.assign_advice(
                || format!("assign pad start flag {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*is_pad_start as u64)),
            )?;
        }

        for (idx, (is_pad_end, column)) in is_pad_ends.iter().zip(self.is_pad_ends.iter()).enumerate() {
            region.assign_advice(
                || format!("assign pad end flag {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*is_pad_end as u64)),
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
    pub(crate) is_pads: [bool; KECCAK_RATE_IN_BYTES],
    pub(crate) is_pad_starts: [bool; KECCAK_RATE_IN_BYTES],
    pub(crate) is_pad_ends: [bool; KECCAK_RATE_IN_BYTES],
}

impl<F: Field> KeccakPaddingRow<F> {

    fn clone(&self) -> KeccakPaddingRow<F> {
        KeccakPaddingRow::<F> {
            is_pads: self.is_pads,
            is_pad_starts: self.is_pad_starts,
            is_pad_ends: self.is_pad_ends,
            d_lens: self.d_lens,
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

    // [is_pads]    0 (data)   0 (data)  (pad) 1   (pad) 1  (pad) 1
    // [d_bytes]       79         106       128       0        1      [0]*CAPACITY//8
    // [d_lens]      base+1     base+2    base+2   base+2   base+2
    // [rlc] 

    fn generate_padding<F: Field>(data_len: u32) -> KeccakPaddingRow<F> {
        let data_len_offset = data_len % KECCAK_RATE_IN_BYTES as u32;        
        let data_len_offset_usize = data_len_offset as usize;
        let data_len_base = data_len - data_len_offset;

        let mut output = KeccakPaddingRow::<F> {
            is_pads: [false; KECCAK_RATE_IN_BYTES], 
            is_pad_starts: [false; KECCAK_RATE_IN_BYTES], 
            is_pad_ends: [false; KECCAK_RATE_IN_BYTES], 
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

        output.is_pads[0] = data_len_offset_usize == 0;
        output.is_pad_starts[0] = data_len_offset_usize == 0;
        output.is_pad_ends[0] = false;

        output.d_lens[0] = data_len_base + !output.is_pads[0] as u32;
        output.d_rlcs[0] = if output.is_pads[0] {
            output.acc_rlc
        } else {
            output.acc_rlc * output.randomness + F::from(output.d_bytes[0] as u64)
        };

        for i in 1 as usize..KECCAK_RATE_IN_BYTES {
            output.is_pads[i] = {
                if i < data_len_offset_usize {
                    false
                } else {
                    true
                }
            };
            output.d_lens[i] = output.d_lens[i - 1] + !output.is_pads[i] as u32; // add 1 if data
            output.d_rlcs[i] = if output.is_pads[i] {
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
            output.is_pad_starts[data_len_offset_usize] = true;
            output.is_pad_ends[data_len_offset_usize] = true;
        } else {
            output.d_bytes[data_len_offset_usize] = 128;
            output.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 1;
            output.is_pad_starts[data_len_offset_usize] = true;
            output.is_pad_ends[KECCAK_RATE_IN_BYTES - 1] = true;
        }
       
        println!("is_pads: {:?}\n", output.is_pads);
        println!("is_pad_starts: {:?}\n", output.is_pad_starts);
        println!("is_pad_ends: {:?}\n", output.is_pad_ends);
        println!("d_lens: {:?}\n", output.d_lens);
        println!("d_bytes: {:?}\n", output.d_bytes);
        println!("Padding start: {:?}\n", output.d_bytes[data_len_offset_usize]);
        println!("Padding end: {:?}\n", output.d_bytes[KECCAK_RATE_IN_BYTES - 1]);
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
