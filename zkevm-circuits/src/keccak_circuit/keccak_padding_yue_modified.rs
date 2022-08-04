use crate::{evm_circuit::util::constraint_builder::BaseConstraintBuilder, util::Expr};
use eth_types::Field;
use gadgets::util::not;
use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};
use std::{env::var, marker::PhantomData, vec};

const KECCAK_WIDTH: usize = 5 * 5 * 64;
const KECCAK_RATE: usize = 1088;
const KECCAK_RATE_IN_BYTES: usize = KECCAK_RATE / 8;

fn get_degree() -> usize {
    var("DEGREE")
        .unwrap_or_else(|_| "8".to_string())
        .parse()
        .expect("Cannot parse DEGREE env var as usize")
}




// [s]     0        0        1        1        1
// [d]     01001111 01101010 10000000 00000000 00000001
// [len]   1        2        2        2        2
// [rlc] 

// rlc(data) keccak(data) len(data)

// - require_boolean(s[i])
// - require_boolean(s[i] - s[i-1])
// - (s[i] - s[i-1]) * require_equal(d[8*i + 0], 1)
// - s[last] * require_equal(d[last], 1)
// - s[i] * not(s[i]-s[i-1]) * not::expr(s[last]) * require_equal(d[i], 0)
//   -> selectors change a bit for which bit position in the byte we're checking, middle bits are always 0
// - require_equal(len[i-1] + not(s[i]), len[i])
// - require_equal(rlc[i], select(s[i], rlc[i], rlc[i-1]*r + d[i*8..(i+1)*8))
// - require_equal(s[last], q_end)

//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 



pub(crate) struct KeccakPaddingRow<F: Field> {
    pub(crate) q_end: u64,
    pub(crate) d_bits: [u8; KECCAK_WIDTH],
    pub(crate) d_lens: [u32; KECCAK_RATE_IN_BYTES],
    pub(crate) d_rlcs: [F; KECCAK_RATE_IN_BYTES],
    pub(crate) s_flags: [bool; KECCAK_RATE_IN_BYTES],
}


//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 


/// KeccakPaddingConfig
#[derive(Clone, Debug)]
pub struct KeccakPaddingConfig<F> {
    q_enable: Selector,
    q_end: Column<Advice>,
    d_bits: [Column<Advice>; KECCAK_WIDTH], // 1600
    d_lens: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    d_rlcs: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    s_flags: [Column<Advice>; KECCAK_RATE_IN_BYTES],
    randomness: Column<Advice>,

    _marker: PhantomData<F>,
}

impl<F: Field> KeccakPaddingConfig<F> {
    pub(crate) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let q_enable = meta.selector();
        let q_end = meta.advice_column();
        let d_bits = [(); KECCAK_WIDTH].map(|_| meta.advice_column());
        let d_lens = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let d_rlcs = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let s_flags = [(); KECCAK_RATE_IN_BYTES].map(|_| meta.advice_column());
        let randomness = meta.advice_column();

        meta.create_gate("boolean checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            //TODO: could be removed if combined with keccak circuit?
            for data_bit in d_bits {
                let b = meta.query_advice(data_bit, Rotation::cur());
                cb.require_boolean("input data bit", b);
            }

            for s_flag in s_flags {
                let s = meta.query_advice(s_flag, Rotation::cur());
                cb.require_boolean("boolean state bit", s);
            }

            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_1 = meta.query_advice(s_flags[i - 1], Rotation::cur());

                cb.require_boolean("boolean state switch", s_i - s_i_1);
            }

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("padding bit checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut constraints = vec![];
            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let s_i_1 = meta.query_advice(s_flags[i - 1], Rotation::cur());
                let d_bit_0 = meta.query_advice(d_bits[8 * i], Rotation::cur());
                constraints.push(("begin with 1", (s_i - s_i_1) * (d_bit_0 - 1u64.expr())));

                //  COMMENT FROM BRECHT: No need for constraints I think, can just do these thinks directly on cb. For example
                // let s_padding_start = s_i - s_i_1;
                // cb.condition(s_padding_start, |cb| {
                //     cb.require_equal(d_bit_0, 1u64.expr());
                // });
            }
            let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
            let d_last = meta.query_advice(d_bits[KECCAK_RATE - 1], Rotation::cur());

            constraints.push(("end with 1", s_last * (d_last - 1u64.expr())));

            cb.add_constraints(constraints);
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("intermedium 0 checks", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut sum_padding_bits = 0u64.expr();
            for i in 0..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                sum_padding_bits = d_bits[i * 8..(i + 1) * 8]
                    .iter()
                    .map(|b| meta.query_advice(*b, Rotation::cur()))
                    .fold(sum_padding_bits, |sum, b| sum + s_i.clone() * b);
            }

            // COMMENT FROM BRECHT: This will indeed work here (all data bits are enforced to be boolean so we don't have to worry about overflows
            //  for any practical data size) and will also be a bit more efficient! In the real keccak circuit the data bits will be split over 
            // multiple rows so you'll have to do this check taking that into account (but easy enough it seems).

            cb.add_constraint("sum padding bits == 2", sum_padding_bits - 2u64.expr());
            // COMMENT FROM BRECHT: No require_equal?

            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input len check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut constraints = vec![];
            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let len_i = meta.query_advice(d_lens[i], Rotation::cur());
                let len_i_1 = meta.query_advice(d_lens[i - 1], Rotation::cur());
                constraints.push(("len[i] = len[i-1] + !s_i", len_i - len_i_1 - not::expr(s_i)));

                // COMMENT FROM BRECHT: Easier to read with require_equal (the code will almost be the same as the description :)

            }

            cb.add_constraints(constraints);
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input rlc check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let mut constraints = vec![];
            for i in 1..s_flags.len() {
                let s_i = meta.query_advice(s_flags[i], Rotation::cur());
                let rlc_i = meta.query_advice(d_rlcs[i], Rotation::cur());
                let rlc_i_1 = meta.query_advice(d_rlcs[i - 1], Rotation::cur());
                let r = meta.query_advice(randomness, Rotation::cur());
                let input_byte_i = d_bits[i * 8..(i + 1) * 8]
                    .iter()
                    .map(|bit| meta.query_advice(*bit, Rotation::cur()))
                    .fold(0u64.expr(), |v, b| v * 2u64.expr() + b);
                constraints.push((
                    "rlc[i] = rlc[i-1]*r if s == 0 else rlc[i]",
                    rlc_i.clone()
                        - (rlc_i.clone() * s_i.clone()
                            + (rlc_i_1 * r + input_byte_i) * not::expr(s_i.clone())),
                ));


                // COMMENT FROM BRECHT: cb.require_equal(rlc_i, select::expr(s_i, rlc_i_1, rlc_i_1 * r + input_byte_i)).

            }

            cb.add_constraints(constraints);
            cb.gate(meta.query_selector(q_enable))
        });

        meta.create_gate("input ending check", |meta| {
            let mut cb = BaseConstraintBuilder::new(5);

            let s_last = meta.query_advice(s_flags[s_flags.len() - 1], Rotation::cur());
            let q_end = meta.query_advice(q_end, Rotation::cur());

            cb.require_equal("s_last == q_end", s_last, q_end);
            cb.gate(meta.query_selector(q_enable))
        });

        KeccakPaddingConfig {
            q_enable,
            q_end,
            d_bits,
            d_lens,
            d_rlcs,
            s_flags,
            randomness,
            _marker: PhantomData,
        }
    }

    pub(crate) fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        _size: usize,
        keccak_padding_row: &KeccakPaddingRow<F>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign keccak rounds",
            |mut region| {
                self.set_row(
                    &mut region,
                    0,
                    keccak_padding_row.q_end,
                    keccak_padding_row.d_bits,
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
        d_bits: [u8; KECCAK_WIDTH],
        d_lens: [u32; KECCAK_RATE_IN_BYTES],
        d_rlcs: [F; KECCAK_RATE_IN_BYTES],
        s_flags: [bool; KECCAK_RATE_IN_BYTES],
        randomness: F,
    ) -> Result<(), Error> {
        self.q_enable.enable(region, offset)?;

        // Input bits w/ padding
        for (idx, (bit, column)) in d_bits.iter().zip(self.d_bits.iter()).enumerate() {
            region.assign_advice(
                || format!("assign input data bit {} {}", idx, offset),
                *column,
                offset,
                || Ok(F::from(*bit as u64)),
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
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 



/// KeccakPaddingCircuit 
#[derive(Default)]
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
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////////////////////////////////// 

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::*;
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr};

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
// [d_bits]     01001111 01101010 10000000 00000000 00000001  [0]*CAPACITY
// [d_lens]      base+1   base+2   base+2   base+2   base+2
// [rlc] 

    fn generate_padding<F: Field>(data_len: u32) -> KeccakPaddingRow<F> {
        let mut output = KeccakPaddingRow::<F> {
            s_flags: [false; KECCAK_RATE_IN_BYTES], 
            d_lens: [0; KECCAK_RATE_IN_BYTES], 
            d_bits: [0; KECCAK_WIDTH],
            d_rlcs: [F::from(0u64); KECCAK_RATE_IN_BYTES],
            q_end: 1u64,
        };
        // let s_bits_len = data_len as usize * 8;

        let data_len_offset = data_len % KECCAK_RATE_IN_BYTES as u32;
        // let data_len_base_remove = (data_len / KECCAK_RATE_IN_BYTES as u32) * KECCAK_RATE_IN_BYTES as u32;
        let data_len_base = data_len - data_len_offset;
        // assert_eq!(data_len_base_remove, data_len_base);

        output.s_flags[0] = data_len_offset == 0u32;
        output.d_lens[0] = data_len_base + !output.s_flags[0] as u32;

        for i in 1 as usize..KECCAK_RATE_IN_BYTES {
            output.s_flags[i] = { // set s_flags 
                if (i as u32) < data_len_offset {
                    false
                } else {
                    true
                }
            };
            output.d_lens[i] = output.d_lens[i - 1] + !output.s_flags[i] as u32; // add 1 if data
        }

        // for i in s_bits_len..KECCAK_RATE {
        //     output.d_bits[i-] = 0u8;
        // }
        // output.d_bits[s_bits_len] = 1;
        // output.d_bits[KECCAK_RATE - 1] = 1;

        let data_len_offset_bits = data_len_offset as usize * 8;
        for i in data_len_offset_bits..KECCAK_RATE {
            output.d_bits[i] = 0u8;
        }
        output.d_bits[data_len_offset_bits] = 1;
        output.d_bits[KECCAK_RATE - 1] = 1;

        println!("{:?}", output.s_flags);
        println!("{:?}", output.d_lens);
        println!("{:?}", output.d_bits);
        output
    }

    static K: u32 = 8;

    #[test]
    fn bit_keccak_len_0() {
        let input = generate_padding::<Fr>(0);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_1() {
        let input = generate_padding::<Fr>(1);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_135() {
        let input = generate_padding::<Fr>(135);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_len_300() {
        let input = generate_padding::<Fr>(300);
        verify::<Fr>(K, vec![input], true);
    }

    #[test]
    fn bit_keccak_invalid_padding_begin() {
        // first bit is 0
        let mut input = generate_padding::<Fr>(11);
        input.d_bits[11 * 8] = 0u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn bit_keccak_invalid_padding_end() {
        // last bit is 0
        let mut input = generate_padding::<Fr>(73);
        input.d_bits[KECCAK_RATE - 1] = 0u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn bit_keccak_invalid_padding_mid() {
        // some 1 in padding
        let mut input = generate_padding::<Fr>(123);
        input.d_bits[KECCAK_RATE - 2] = 1u8;
        verify::<Fr>(K, vec![input], false);
    }

    #[test]
    fn bit_keccak_invalid_input_len() {
        // wrong len
        let mut input = generate_padding::<Fr>(123);
        input.d_lens[124] = 124;
        verify::<Fr>(K, vec![input], false);
    }
}
