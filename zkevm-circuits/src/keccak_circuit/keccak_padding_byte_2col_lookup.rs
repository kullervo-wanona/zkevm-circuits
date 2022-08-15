use crate::{
    evm_circuit::{
        util::{constraint_builder::BaseConstraintBuilder, select},
    },
    util::Expr,
};

use eth_types::Field;
use gadgets::util::not;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Table},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Selector, TableColumn, Expression,
    },
    poly::Rotation,
};
use std::{env::var, marker::PhantomData, vec};
use rand::{thread_rng, Fill};

const KECCAK_RATE: usize = 1088;
const KECCAK_RATE_IN_BYTES: usize = KECCAK_RATE / 8;

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}

// [is_pads]    0 (data)   0 (data)  (pad) 1   (pad) 1  (pad) 1
// [d_bytes]       79         106       128       0        1  
// [d_lens]      base+1     base+2    base+2   base+2   base+2
// [rlc] 

#[derive(Debug, Clone)]
#[allow(missing_docs)]
pub struct PaddingCombinationsConfig<F> {
    pub byte_col: TableColumn,
    pub is_pad_col: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: Field> PaddingCombinationsConfig<F> {

    pub(crate) fn configure(cs: &mut ConstraintSystem<F>) -> Self {
        Self {
            byte_col: cs.lookup_table_column(),
            is_pad_col: cs.lookup_table_column(),
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign_table_row(&self, mut table: Table<'_, F>, row_id: usize, 
                                   byte_val: u64, is_pad_val: u64, 
                                  ) -> Result<(), Error> {
        
        table.assign_cell(|| format!("byte_col_[row={}]", row_id), self.byte_col, row_id, || Ok(F::from(byte_val)))?;
        table.assign_cell(|| format!("is_pad_col_[row={}]", row_id), self.is_pad_col, row_id, || Ok(F::from(is_pad_val)))?;
        
        Ok(())
    }
    pub(crate) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        const K: u64 = 256;
        layouter.assign_table(
            // The table will restrict padding flags to {0,1} and data/padding bytes to [0, 255].
            // Only particular combinations are allowed,
            // (is_pad_col, byte_col)
            // 0 | [all 256 possible byte values]
            // 1 | 128 // start-exclusive
            // 1 | 129 // start-end
            // 1 | 0 // mid
            // 1 | 1 // end-exclusive

            || "byte-is_pad combination table",
            |mut table: Table<'_, F>| {
                for i in 0..K {
                    //// byte = [0, 255], is_pad = 0, actual input data
                    // self.assign_table_row(table, i as usize, i, 0);
                    table.assign_cell(|| "byte_col_[i=0:K-1]", self.byte_col, i as usize, || Ok(F::from(i)))?;
                    table.assign_cell(|| "is_pad_col_[i=0:K-1]", self.is_pad_col, i as usize, || Ok(F::from(0)))?;
                }
                
                //// byte = 0, is_pad = 1, the middle of the padding case
                // self.assign_table_row(table, K as usize, 0, 1);
                table.assign_cell(|| "byte_col_[i=K]", self.byte_col, (K) as usize, || Ok(F::from(0)))?;
                table.assign_cell(|| "is_pad_col_[i=K]", self.is_pad_col, (K) as usize, || Ok(F::from(1)))?;

                //// byte = 128, is_pad = 1, the beginning of the padding separate from end case
                // self.assign_table_row(table, (K + 1) as usize, 128, 1);
                table.assign_cell(|| "byte_col_[i=K+1]", self.byte_col, (K + 1) as usize, || Ok(F::from(128)))?;
                table.assign_cell(|| "is_pad_col_[i=K+1]", self.is_pad_col, (K + 1) as usize, || Ok(F::from(1)))?;
            
                //// byte = 129, is_pad = 1, the beginning of the padding same as end case
                // self.assign_table_row(table, (K + 2) as usize, 129, 1);
                table.assign_cell(|| "byte_col_[i=K+2]", self.byte_col, (K + 2) as usize, || Ok(F::from(129)))?;
                table.assign_cell(|| "is_pad_col_[i=K+2]", self.is_pad_col, (K + 2) as usize, || Ok(F::from(1)))?;

                //// byte = 1, is_pad = 1, the end of the padding separate from beginning case
                // self.assign_table_row(table, (K + 3) as usize, 1, 1);
                table.assign_cell(|| "byte_col_[i=K+3]", self.byte_col, (K + 3) as usize, || Ok(F::from(1)))?;
                table.assign_cell(|| "is_pad_col_[i=K+3]", self.is_pad_col, (K + 3) as usize, || Ok(F::from(1)))?;

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
    padding_combinations_table: PaddingCombinationsConfig<F>,

    q_enable: Selector,
    randomness: Column<Advice>,
    acc_len: Column<Advice>,
    acc_rlc: Column<Advice>,
    is_pads: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    d_bytes: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    d_lens: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    d_rlcs: [Column<Advice>; KECCAK_RATE_IN_BYTES],

    _marker: PhantomData<F>,
}

impl<F: Field> KeccakPaddingConfig<F> {
    pub(crate) fn configure(cs: &mut ConstraintSystem<F>) -> Self {
        let padding_combinations_table = PaddingCombinationsConfig::<F>::configure(cs);

        let q_enable = cs.selector();
        let randomness = cs.advice_column();        
        let acc_len = cs.advice_column();        
        let acc_rlc = cs.advice_column();        
        let is_pads = [(); KECCAK_RATE_IN_BYTES].map(|_| cs.advice_column());
        let d_bytes = [(); KECCAK_RATE_IN_BYTES].map(|_| cs.advice_column());
        let d_lens = [(); KECCAK_RATE_IN_BYTES].map(|_| cs.advice_column());
        let d_rlcs = [(); KECCAK_RATE_IN_BYTES].map(|_| cs.advice_column());

            
        // Check that (padding flag, data/padding byte) combinations are restricted to the combinations in padding_combinations_table.        
        // The table will estrict padding flags to {0,1} and data/padding bytes to [0, 255].
        // Only particular combinations are allowed, check PaddingCombinationsConfig load method comments.
        for i in 0..is_pads.len() {
            cs.lookup("Check allowed data/padding/flag combinations", |virt_cells| {
                let is_pad_curr = virt_cells.query_advice(is_pads[i], Rotation::cur());
                let d_bytes_curr = virt_cells.query_advice(d_bytes[i], Rotation::cur());

                // let q_enable = virt_cells.query_selector(q_enable);
                // vec![
                //     (q_enable.clone() * d_bytes_curr, padding_combinations_table.byte_col),
                //     (q_enable.clone() * is_pad_curr, padding_combinations_table.is_pad_col),
                // ]
                vec![
                    (d_bytes_curr, padding_combinations_table.byte_col),
                    (is_pad_curr, padding_combinations_table.is_pad_col),
                ]
            });
        };

        cs.create_gate("Check inter-cell relationships", |virt_cells| {
            let mut cb = BaseConstraintBuilder::new(5);

            let acc_len_prev = virt_cells.query_advice(acc_len, Rotation::cur());
            let acc_rlc_prev = virt_cells.query_advice(acc_rlc, Rotation::cur());
            
            let is_pad_last = virt_cells.query_advice(is_pads[is_pads.len() - 1], Rotation::cur());
            let is_pad_last_prev = virt_cells.query_advice(is_pads[is_pads.len() - 2], Rotation::cur());
            
            let is_start_end_separate = is_pad_last.clone() * is_pad_last_prev.clone(); 
            let is_start_end_same = is_pad_last.clone() * not::expr(is_pad_last_prev.clone());

            let d_last_byte = virt_cells.query_advice(d_bytes[is_pads.len() - 1], Rotation::cur());

            // // Ensure that if q_end is true (last data or padding block to be sent to the hash function), 
            // // the last padding flag is 1 and zero otherwise.)
            // // Everything cascades from this condition.
            // cb.require_equal("is_pad_last == q_end", is_pad_last.clone(), q_end.clone());

            // Based on the value of is_start_end_separate, which is 1 if the last two padding flags are 1, 
            // constrain the last data+padding byte to 1. 
            cb.condition(is_start_end_separate.clone(), |cb| {
                cb.require_equal("Check d_bytes padding start-end separate", d_last_byte.clone(), 1u64.expr());
            });

            // Based on the value of is_start_end_same, which is 1 if the last two padding flags are (0, 1), 
            // constrain the last data+padding byte to 129. 
            cb.condition(is_start_end_same.clone(), |cb| {
                cb.require_equal("Check d_bytes padding start-end the same", d_last_byte.clone(), 129u64.expr());
            });

            // This is where most of the constraints are effectuated for the padding flags and data/padding bytes. 
            for i in 0..is_pads.len() {
                let r = virt_cells.query_advice(randomness, Rotation::cur());

                let is_pad_curr = virt_cells.query_advice(is_pads[i], Rotation::cur());
                let d_byte_curr = virt_cells.query_advice(d_bytes[i], Rotation::cur());
                let d_len_curr = virt_cells.query_advice(d_lens[i], Rotation::cur());
                let d_rlc_curr = virt_cells.query_advice(d_rlcs[i], Rotation::cur());
                let is_pad_prev: Expression<F>;

                if i == 0 {
                    is_pad_prev = 0u64.expr();
                } else {
                    is_pad_prev = virt_cells.query_advice(is_pads[i - 1], Rotation::cur());
                }
                let is_padding_step = is_pad_curr.clone() - is_pad_prev.clone();

                // First, we enforce monotonicity to the padding flags. Combined with the table restrictions, 
                // this ensures that padding flags are [0]*[1]*, zeroes followed by ones.
                cb.require_boolean("Check that padding flags are monotonically non-decreasing.", is_padding_step.clone());
                
                // Based on the value of is_start_end_same and is_start_end_separate, we go through each element and 
                // detect if there is a step function change in the padding flags, and constrain the respective
                // byte to 129 or 128 respectively. 
                cb.condition(is_padding_step.clone() * is_start_end_separate.clone(), |cb| {
                    cb.require_equal("Check d_bytes padding start", d_byte_curr.clone(), 128u64.expr());
                });

                cb.condition(is_padding_step.clone() * is_start_end_same.clone(), |cb| {
                    cb.require_equal("Check d_bytes padding start", d_byte_curr.clone(), 129u64.expr());
                });
                
                // Further if there is no step function change and the padding flag is 1, then we are in the intermediate
                // regions of the padding, and therefore need to constrain the respective byte to zero (except last element). 
                if i < (is_pads.len() - 1) {
                    cb.condition(not::expr(is_padding_step.clone()) * is_pad_curr.clone(), |cb| {
                        cb.require_equal("Check d_bytes padding intermediate", d_byte_curr.clone(), 0u64.expr());
                    });
                }

                if i == 0 {
                    cb.require_equal("d_len[0] = acc_len_prev + !s_0", d_len_curr.clone(), acc_len_prev.clone() + not::expr(is_pad_curr.clone()));
                    cb.require_equal("d_rlc[0] = acc_rlc_prev*r if s_0 == 0 else d_rlc[i]", d_rlc_curr.clone(), 
                    select::expr(is_pad_curr.clone(), d_rlc_curr.clone(), acc_rlc_prev.clone() * r.clone() + d_byte_curr.clone()));

                } else {
                    let d_len_prev = virt_cells.query_advice(d_lens[i - 1], Rotation::cur());                
                    let d_rlc_prev = virt_cells.query_advice(d_rlcs[i - 1], Rotation::cur());
    
                    // Check that d_len elements are increasing by one if they do not correspond to padding 
                    cb.require_equal("d_len[i] = d_len[i-1] + !s_i", d_len_curr.clone(), d_len_prev.clone() + not::expr(is_pad_curr.clone()));

                    // Check that rlc elements are changing properly if they do not correspond to padding 
                    cb.require_equal("d_rlc[i] = d_rlc[i-1]*r if s == 0 else d_rlc[i]", d_rlc_curr.clone(), 
                    select::expr(is_pad_curr.clone(), d_rlc_curr.clone(), d_rlc_prev.clone() * r.clone() + d_byte_curr.clone()));
                } 

            }    
            cb.gate(virt_cells.query_selector(q_enable))
        });

        KeccakPaddingConfig {
            padding_combinations_table, 
            q_enable,
            randomness,
            acc_len,
            acc_rlc,
            is_pads,
            d_bytes,
            d_lens,
            d_rlcs,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        randomness: F,
        keccak_block_witness: KeccakBlockWitness<F>,
    ) -> Result<(), Error> {

        self.padding_combinations_table.load(&mut layouter)?;

        layouter.assign_region(
            || "assign keccak padded data",
            |mut region| {
                self.set_row(
                    &mut region,
                    0,
                    randomness,
                    keccak_block_witness,
                )?;
                Ok(())
            },
        )
    }

    fn set_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        randomness: F,
        keccak_block_witness: KeccakBlockWitness<F>,
    ) -> Result<(), Error> {
        self.q_enable.enable(region, offset)?;

        region.assign_advice(
            || format!("assign randomness {}", offset),
            self.randomness,
            offset,
            || Ok(randomness),
        )?;

        region.assign_advice(
            || format!("assign acc_len {}", offset),
            self.acc_len,
            offset,
            || Ok(F::from(keccak_block_witness.acc_len as u64)),
        )?;

        region.assign_advice(
            || format!("assign acc_rlc {}", offset),
            self.acc_rlc,
            offset,
            || Ok(keccak_block_witness.acc_rlc),
        )?;

        for (idx, (is_pad, column)) in keccak_block_witness.is_pads.iter().zip(self.is_pads.iter()).enumerate() {
            region.assign_advice(
                || format!("assign is_pads {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*is_pad as u64)),
            )?;
        }

        for (idx, (byte, column)) in keccak_block_witness.d_bytes.iter().zip(self.d_bytes.iter()).enumerate() {
            region.assign_advice(
                || format!("assign d_bytes {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*byte as u64)),
            )?;
        }

        for (idx, (d_len, column)) in keccak_block_witness.d_lens.iter().zip(self.d_lens.iter()).enumerate() {
            region.assign_advice(
                || format!("assign d_lens {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*d_len as u64)),
            )?;
        }

        for (idx, (d_rlc, column)) in keccak_block_witness.d_rlcs.iter().zip(self.d_rlcs.iter()).enumerate() {
            region.assign_advice(
                || format!("assign d_rlcs {} {}", idx, offset),
                *column,
                offset,
                || Ok(*d_rlc),
            )?;
        }

        Ok(())
    }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 

#[derive(Copy, Clone)]
pub(crate) struct KeccakBlockWitness<F: Field> {
    pub(crate) randomness: F,
    pub(crate) acc_len: u32,
    pub(crate) acc_rlc: F,
    pub(crate) is_pads: [bool; KECCAK_RATE_IN_BYTES],
    pub(crate) d_bytes: [u8; KECCAK_RATE_IN_BYTES],
    pub(crate) d_lens: [u32; KECCAK_RATE_IN_BYTES],
    pub(crate) d_rlcs: [F; KECCAK_RATE_IN_BYTES],
}

impl<F: Field> Default for KeccakBlockWitness<F> {
    fn default() -> KeccakBlockWitness<F> {
        KeccakBlockWitness::<F>::generate_all_witnesses(0, 0)[0]
    }
}

#[allow(unused_assignments)]
impl<F: Field> KeccakBlockWitness<F> {

    // [is_pads]    0 (data)   0 (data)  (pad) 1   (pad) 1  (pad) 1
    // [d_bytes]       79         106       128       0        1  
    // [d_lens]      base+1     base+2    base+2   base+2   base+2
    // [d_rlc] 

    fn generate_data_bytes(overall_data_len: u32) -> Vec<u8> {
        let mut d_bytes_all = vec![0u8; overall_data_len as usize];
        let mut rng = thread_rng();
        d_bytes_all.try_fill(&mut rng).unwrap();
        d_bytes_all
    }

    fn generate_all_witnesses(overall_data_len: u32, verbosity: u32) -> Vec<KeccakBlockWitness<F>> {
        let d_bytes_all = KeccakBlockWitness::<F>::generate_data_bytes(overall_data_len);
        let overall_data_len_usize = overall_data_len as usize;
        let n_blocks = overall_data_len_usize / KECCAK_RATE_IN_BYTES + 1; 
        if verbosity == 2 {
            println!("n_blocks: {:?}", n_blocks);
            println!("overall_data_len_usize: {:?}", overall_data_len_usize);
        }

        let mut all_witnesses = Vec::with_capacity(n_blocks);
        let mut acc_len = 0u32;
        let mut acc_rlc = F::one();
        let mut d_bytes_curr = vec![];

        for i in 0..n_blocks {
            let block_ind_start = i*KECCAK_RATE_IN_BYTES;
            let block_ind_end = std::cmp::min((i+1)*KECCAK_RATE_IN_BYTES, overall_data_len_usize);
            if verbosity == 2 {
                println!("block_ind_start: {:?}", block_ind_start);
                println!("block_ind_end: {:?}", block_ind_end);
                println!("data_block: {:?}", &d_bytes_all[block_ind_start..block_ind_end]);
            }
            if block_ind_start < d_bytes_all.len() {
                d_bytes_curr = d_bytes_all[block_ind_start..block_ind_end].to_vec();
            } else {
                d_bytes_curr = vec![];
            }

            let curr_block_witness = 
                KeccakBlockWitness::<F>::generate_block_witness(d_bytes_curr, acc_len, acc_rlc, 
                    verbosity == 2 || (verbosity == 1 && i == (n_blocks-1)));
            acc_len = curr_block_witness.d_lens[curr_block_witness.d_lens.len()-1];
            acc_rlc = curr_block_witness.d_rlcs[curr_block_witness.d_rlcs.len()-1];
            all_witnesses.push(curr_block_witness);
        }

        all_witnesses
    }

    fn generate_block_witness(d_bytes_block: Vec<u8>, acc_len: u32, acc_rlc: F, verbose: bool) -> KeccakBlockWitness<F> {
        assert!(d_bytes_block.len() <= KECCAK_RATE_IN_BYTES);

        let mut witness = KeccakBlockWitness::<F> {
            randomness: KeccakPaddingCircuit::r(),
            acc_len: acc_len,
            acc_rlc: acc_rlc,
            is_pads: [false; KECCAK_RATE_IN_BYTES], 
            d_bytes: [0u8; KECCAK_RATE_IN_BYTES],
            d_lens: [0u32; KECCAK_RATE_IN_BYTES], 
            d_rlcs: [F::from(0u64); KECCAK_RATE_IN_BYTES],
        };

        let mut curr_acc_len = acc_len;
        let mut curr_acc_rlc = acc_rlc;
        
        for i in 0..KECCAK_RATE_IN_BYTES {
            if i < d_bytes_block.len() { // data 
                witness.d_bytes[i] = d_bytes_block[i];
                curr_acc_len = curr_acc_len + 1; 
                curr_acc_rlc = curr_acc_rlc * witness.randomness + F::from(witness.d_bytes[i] as u64)
            } else {  // padding 
                witness.is_pads[i] = true;
            }
            witness.d_lens[i] = curr_acc_len;
            witness.d_rlcs[i] = curr_acc_rlc;
        }

        if d_bytes_block.len() < KECCAK_RATE_IN_BYTES { // some padding 
            if d_bytes_block.len() == (KECCAK_RATE_IN_BYTES - 1) {
                witness.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 129;
            } else {
                witness.d_bytes[d_bytes_block.len()] = 128;
                witness.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 1;
            }
        }

        if verbose {
            println!("\nWITNESS START");
            KeccakBlockWitness::<F>::print_keccac_padding_witness(witness, d_bytes_block.len());
            println!("WITNESS END\n");
        }
        witness
    }

    fn print_keccac_padding_witness(witness: KeccakBlockWitness<F>, d_bytes_block_len: usize) {
        println!("acc_len: {:?}", witness.acc_len);
        println!("is_pads: {:?}", witness.is_pads);
        println!("d_bytes: {:?}", witness.d_bytes);
        println!("d_lens: {:?}", witness.d_lens);
        if d_bytes_block_len < KECCAK_RATE_IN_BYTES { // some padding 
            println!("Padding start: {:?}", witness.d_bytes[d_bytes_block_len]);
            println!("Padding end: {:?}", witness.d_bytes[KECCAK_RATE_IN_BYTES - 1]);
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
    size: usize,
    input_keccak_block_witness: KeccakBlockWitness<F>,
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
            KeccakPaddingCircuit::r(),
            self.input_keccak_block_witness,
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

    fn verify<F: Field>(k: u32, input_keccak_block_witnesses: Vec<KeccakBlockWitness<F>>, joint_success: bool) {
        
        let mut all_succeeded = true;
        for i in 0..input_keccak_block_witnesses.len() {
            println!("Verifying block {}", (i+1));

            let circuit = KeccakPaddingCircuit::<F> {
                size: 2usize.pow(k),
                input_keccak_block_witness: input_keccak_block_witnesses[i],
                _marker: PhantomData,
            };
            let prover = MockProver::<F>::run(k, &circuit, vec![]).unwrap();


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
            all_succeeded = all_succeeded && err.is_ok();
        }
        assert_eq!(all_succeeded, joint_success);

    }

    static LOG_MAX_ROW: u32 = 10;

    #[test]
    fn test_case_0() {
        let data_offset = 0;
        let witness_all = 
            KeccakBlockWitness::<Fr>::generate_all_witnesses((KECCAK_RATE_IN_BYTES+data_offset) as u32, 1);

        // witness_last_block.is_pads =   [1]*136
        // witness_last_block.d_bytes = [128]*1 [0]*134 [1]*1
        let witness_last_block = witness_all[witness_all.len()-1];

        verify::<Fr>(LOG_MAX_ROW, witness_all, true);

        // check constraints for padding-start is_pads
        let mut witness_last_block_1 = witness_last_block;
        witness_last_block_1.is_pads[data_offset] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_1], false);

        // check constraints for padding-start d_bytes
        let mut witness_last_block_2 = witness_last_block;
        witness_last_block_2.d_bytes[data_offset] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_2], false);

        // check constraints for padding-mid is_pads
        let mut witness_last_block_3 = witness_last_block;
        witness_last_block_3.is_pads[data_offset + 2] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_3], false);

        // check constraints for padding-mid d_bytes
        let mut witness_last_block_4 = witness_last_block;
        witness_last_block_4.d_bytes[data_offset + 2] = 1u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_4], false);

        // check constraints for padding-end is_pads
        let mut witness_last_block_5 = witness_last_block;
        witness_last_block_5.is_pads[KECCAK_RATE_IN_BYTES - 1] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_5], false);

        // check constraints for padding-end d_bytes
        let mut witness_last_block_6 = witness_last_block;
        witness_last_block_6.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_6], false);

        // check constraints for padding d_lens
        let mut witness_last_block_8 = witness_last_block;
        witness_last_block_8.d_lens[data_offset + 1] = 4 as u32; 
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_8], false);

        // no constraints for padding RLC
        let mut witness_last_block_10 = witness_last_block;
        witness_last_block_10.d_rlcs[data_offset + 2] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_10], true);

        // check constraints for acc_len
        let mut witness_last_block_11 = witness_last_block;
        witness_last_block_11.acc_len = 0u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_11], false);

        // no constraints for acc_rlc since the last block is all padding
        let mut witness_last_block_12 = witness_last_block;
        witness_last_block_12.acc_rlc = Fr::from(0u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_12], true);
        
    }

    #[test]
    fn test_case_1() {
        let data_offset = 1;
        let witness_all = 
            KeccakBlockWitness::<Fr>::generate_all_witnesses((KECCAK_RATE_IN_BYTES+data_offset) as u32, 1);

        // witness_last_block.is_pads =   [0]*1       [1]*135
        // witness_last_block.d_bytes = [data]*1 [128]*1 [0]*133 [1]*1
        let witness_last_block = witness_all[witness_all.len()-1];

        verify::<Fr>(LOG_MAX_ROW, witness_all, true);

        // check constraints for padding-start is_pads
        let mut witness_last_block_1 = witness_last_block;
        witness_last_block_1.is_pads[data_offset] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_1], false);

        // check constraints for padding-start d_bytes
        let mut witness_last_block_2 = witness_last_block;
        witness_last_block_2.d_bytes[data_offset] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_2], false);

        // check constraints for padding-mid is_pads
        let mut witness_last_block_3 = witness_last_block;
        witness_last_block_3.is_pads[data_offset + 2] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_3], false);

        // check constraints for padding-mid d_bytes
        let mut witness_last_block_4 = witness_last_block;
        witness_last_block_4.d_bytes[data_offset + 2] = 1u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_4], false);

        // check constraints for padding-end is_pads
        let mut witness_last_block_5 = witness_last_block;
        witness_last_block_5.is_pads[KECCAK_RATE_IN_BYTES - 1] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_5], false);

        // check constraints for padding-end d_bytes
        let mut witness_last_block_6 = witness_last_block;
        witness_last_block_6.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_6], false);

        // check constraints for non-padding d_lens
        let mut witness_last_block_7 = witness_last_block;
        witness_last_block_7.d_lens[0] = 4 as u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_7], false);
        
        // check constraints for padding d_lens
        let mut witness_last_block_8 = witness_last_block;
        witness_last_block_8.d_lens[data_offset + 1] = 4 as u32; 
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_8], false);

        // check constraints for non-padding RLC
        let mut witness_last_block_9 = witness_last_block;
        witness_last_block_9.d_rlcs[0] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_9.clone()], false);

        // no constraints for padding RLC
        let mut witness_last_block_10 = witness_last_block;
        witness_last_block_10.d_rlcs[data_offset + 2] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_10], true);

        // check constraints for acc_len
        let mut witness_last_block_11 = witness_last_block;
        witness_last_block_11.acc_len = 0u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_11], false);

        // check constraints for acc_rlc
        let mut witness_last_block_12 = witness_last_block;
        witness_last_block_12.acc_rlc = Fr::from(0u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_12], false);
        
    }

    #[test]
        fn test_case_135() {
        let data_offset = 135;
        let witness_all = 
            KeccakBlockWitness::<Fr>::generate_all_witnesses((KECCAK_RATE_IN_BYTES+data_offset) as u32, 1);

        // witness_last_block.is_pads =   [0]*135       [1]*1
        // witness_last_block.d_bytes = [data]*135     [129]*1
        let witness_last_block = witness_all[witness_all.len()-1];

        verify::<Fr>(LOG_MAX_ROW, witness_all, true);

        // check constraints for padding-start/end is_pads
        let mut witness_last_block_1 = witness_last_block;
        witness_last_block_1.is_pads[data_offset] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_1], false);

        // check constraints for padding-start/end d_bytes
        let mut witness_last_block_2 = witness_last_block;
        witness_last_block_2.d_bytes[data_offset] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_2], false);

        // check constraints for non-padding d_lens
        let mut witness_last_block_7 = witness_last_block;
        witness_last_block_7.d_lens[2] = 4 as u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_7], false);
        
        // check constraints for padding d_lens
        let mut witness_last_block_8 = witness_last_block;
        witness_last_block_8.d_lens[data_offset] = 4 as u32; 
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_8], false);

        // check constraints for non-padding RLC
        let mut witness_last_block_9 = witness_last_block;
        witness_last_block_9.d_rlcs[2] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_9.clone()], false);

        // no constraints for padding RLC
        let mut witness_last_block_10 = witness_last_block;
        witness_last_block_10.d_rlcs[data_offset] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_10], true);

        // check constraints for acc_len
        let mut witness_last_block_11 = witness_last_block;
        witness_last_block_11.acc_len = 0u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_11], false);

        // check constraints for acc_rlc
        let mut witness_last_block_12 = witness_last_block;
        witness_last_block_12.acc_rlc = Fr::from(0u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_12], false);
        
        
    }

    #[test]
    fn test_case_common() {
        let data_offset = 123;
        
        let witness_all = 
            KeccakBlockWitness::<Fr>::generate_all_witnesses((KECCAK_RATE_IN_BYTES+data_offset) as u32, 1);
        verify::<Fr>(LOG_MAX_ROW, witness_all.clone(), true);

        let mut witness_all_clone_1 = witness_all.clone();
        witness_all_clone_1[0].acc_len = 3u32;
        verify::<Fr>(LOG_MAX_ROW, witness_all_clone_1, false);

        let mut witness_all_clone_2 = witness_all.clone();
        witness_all_clone_2[0].acc_rlc = Fr::from(5u64);
        verify::<Fr>(LOG_MAX_ROW, witness_all_clone_2, false);

        // witness_last_block.is_pads =   [0]*123       [1]*13
        // witness_last_block.d_bytes = [data]*123 [128]*1 [0]*12 [1]*1
        let witness_last_block = witness_all.clone()[witness_all.len()-1];

        // check constraints for padding-start is_pads
        let mut witness_last_block_1 = witness_last_block;
        witness_last_block_1.is_pads[data_offset] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_1], false);

        // check constraints for padding-start d_bytes
        let mut witness_last_block_2 = witness_last_block;
        witness_last_block_2.d_bytes[data_offset] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_2], false);

        // check constraints for padding-mid is_pads
        let mut witness_last_block_3 = witness_last_block;
        witness_last_block_3.is_pads[data_offset + 2] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_3], false);

        // check constraints for padding-mid d_bytes
        let mut witness_last_block_4 = witness_last_block;
        witness_last_block_4.d_bytes[data_offset + 2] = 1u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_4], false);

        // check constraints for padding-end is_pads
        let mut witness_last_block_5 = witness_last_block;
        witness_last_block_5.is_pads[KECCAK_RATE_IN_BYTES - 1] = false;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_5], false);

        // check constraints for padding-end d_bytes
        let mut witness_last_block_6 = witness_last_block;
        witness_last_block_6.d_bytes[KECCAK_RATE_IN_BYTES - 1] = 0u8;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_6], false);

        // check constraints for non-padding d_lens
        let mut witness_last_block_7 = witness_last_block;
        witness_last_block_7.d_lens[2] = 4 as u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_7], false);
        
        // check constraints for padding d_lens
        let mut witness_last_block_8 = witness_last_block;
        witness_last_block_8.d_lens[data_offset + 1] = 4 as u32; 
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_8], false);

        // check constraints for non-padding RLC
        let mut witness_last_block_9 = witness_last_block;
        witness_last_block_9.d_rlcs[2] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_9.clone()], false);

        // no constraints for padding RLC
        let mut witness_last_block_10 = witness_last_block;
        witness_last_block_10.d_rlcs[data_offset + 2] = Fr::from(4u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_10], true);

        // check constraints for acc_len
        let mut witness_last_block_11 = witness_last_block;
        witness_last_block_11.acc_len = 0u32;
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_11], false);

        // check constraints for acc_rlc
        let mut witness_last_block_12 = witness_last_block;
        witness_last_block_12.acc_rlc = Fr::from(0u64);
        verify::<Fr>(LOG_MAX_ROW, vec![witness_last_block_12], false);
        
        
    }


}
