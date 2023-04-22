#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unreachable_code)]

//! A circuit is a layout of columns over multiple rows, capable of building or
//! defining their own custom constraints. In the [`zkEVM`] architecture, many
//! such circuits (individually termed as sub-circuits) are placed within a
//! super-circuit. When a circuit encounters an expensive operation, it can
//! outsource the verification effort to another circuit through the usage of
//! lookup arguments.
//!
//! For instance, the [`EVM-circuit`] would like to verify the output of a call
//! to the precompiled contract [`SHA2-256`], which in itself is an expensive
//! operation to verify. So in order to separate out the verification logic and
//! build a more developer-friendly approach, the EVM circuit would use the
//! SHA2-256 circuit's table via lookups to communicate simply the input-output
//! relationship, outsourcing the effort of verifying the relationship itself
//! to the SHA2-256 circuit.
//!
//! In the sha2-256-circuit crate, we export the SHA2-256 circuit's config `Sha2Config`,
//! and the table within it (that other circuits can use as a lookup argument)
//! `Sha2Table`. The config type defines the layout of the circuit, the various
//! named columns in the circuit's layout, and the `configure` method is meant
//! to define the relationship between those columns over its neighbouring rows.
//!
//! For instance, for the `id` field to be an incremental field, one may specify
//! the following relationship:
//! ```
//! # impl<F: FieldExt> Sha2Config<F> {
//!     pub fn configure(meta: &mut ConstraintSystem<F>, table: Sha2Table) -> Self {
//!         meta.create_gate("validity check over all rows", |meta| {
//!             let mut cb = BaseConstraintBuilder::default();
//!             cb.require_equal(
//!                 "id field is incremental, i.e. id::cur + 1 == id::next",
//!                 meta.query_advice(table.id, Rotation::cur()) + 1.expr(),
//!                 meta.query_advice(table.id, Rotation::next()),
//!             );
//!             cb.gate(1.expr()) // enable this gate over all rows.
//!         });
//!
//!         Self {
//!             table,
//!             _marker: PhantomData,
//!         }
//!     }
//! # }
//! ```
//!
//! We also describe how the EVM circuit would lookup to the SHA2 circuit via lookup
//! arguments [`here`]. Currently, the table is a dummy column named `id`.
//!
//! The following tasks are expected to be done:
//! - Define the layout of the SHA2-256 circuit through columns in `Sha2Config`.
//! - Define the lookup argument exposed by SHA2-256 circuit via `Sha2Table`.
//! - Define verification logic over rows of the circuit by constraining the relationship
//!   between the columns.
//! - Assign witness data to the circuit via the `load` method.
//! - Test the verification logic in the circuit.
//!
//! [`zkEVM`]: https://privacy-scaling-explorations.github.io/zkevm-docs/introduction.html
//! [`EVM-circuit`]: https://github.com/scroll-tech/zkevm-circuits/blob/scroll-stable/zkevm-circuits/src/evm_circuit.rs
//! [`SHA2-256`]: https://en.wikipedia.org/wiki/SHA-2#Pseudocode
//! [`here`]: https://github.com/scroll-tech/zkevm-circuits/pull/398

use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::Layouter,
    plonk::{Advice, Any, Column, ConstraintSystem, Error},
    poly::Rotation,
};

mod gates;
mod regions;
mod spread_table;
mod utils;

use spread_table::SpreadTableConfig;
use regions::{
    compression::CompressionChip, 
    message_schedule::MessageScheduleChip
};


#[derive(Clone, Debug)]
pub struct Sha2Table {
    id: Column<Advice>,
}

impl Sha2Table {
    pub fn construct<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {
        Self {
            id: meta.advice_column(),
        }
    }

    pub fn columns(&self) -> Vec<Column<Any>> {
        vec![self.id.into()]
    }

    pub fn annotations(&self) -> Vec<String> {
        vec![String::from("id")]
    }
}

#[derive(Clone, Debug)]
pub struct Sha2Config<F: FieldExt> {
    table: Sha2Table,
    cols: Vec<Column<Advice>>,
    spread_table: SpreadTableConfig<F, 16>,
    compression_chip: CompressionChip<F>,
    message_schedule_chip: MessageScheduleChip<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Sha2Config<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>, 
        table: Sha2Table,
    ) -> Self {
        let mut cols: Vec<Column<Advice>> = vec![];
        for i in 0..10 {
            cols.push(meta.advice_column());
            meta.enable_equality(cols[i]);
        }
        let spread_table = SpreadTableConfig::configure(meta);
        let compression_chip = CompressionChip::configure(
            meta, 
            cols[0], cols[1], cols[2], cols[3], cols[4], 
            cols[5], cols[6], cols[7], cols[8], cols[9]
        );
        let message_schedule_chip = MessageScheduleChip::configure(
            meta, cols[0], cols[1], cols[2], cols[3], cols[4], 
            cols[5], cols[6], cols[7], cols[8], cols[9]
        );
        
        meta.lookup(
            "Consistent Lookup 1", 
            |table| {
                let a0 = table.query_advice(cols[0], Rotation::cur());
                let a1 = table.query_advice(cols[1], Rotation::cur());
                let a2 = table.query_advice(cols[2], Rotation::cur());

                vec![
                    (a0, spread_table.tag),
                    (a1, spread_table.table),
                    (a2, spread_table.spread)
                ]
            }
        );

        meta.lookup("Consistent Lookup 2", |table| {

            let sd_abc = table.query_selector(compression_chip.sd_abc.s_abc);
            let sd_efg = table.query_selector(compression_chip.sd_efg.s_efg);
            let a7 = table.query_advice(cols[7], Rotation::cur());
            let a8 = table.query_advice(cols[8], Rotation::cur());

            let flag = sd_abc.clone() + sd_efg.clone() + sd_abc * sd_efg;

            vec![
                (flag.clone() * a7, spread_table.table),
                (flag * a8,         spread_table.spread),
            ]
        });

        Self {
            table,
            cols,
            compression_chip,
            message_schedule_chip,
            spread_table,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Sha2Witness<F> {
    pub inputs: Vec<Vec<u8>>,
    pub _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct Sha2Chip<F: FieldExt> {
    config: Sha2Config<F>,
    data: Sha2Witness<F>,
}

impl<F: FieldExt> Sha2Chip<F> {
    pub fn construct(config: Sha2Config<F>, data: Sha2Witness<F>) -> Self {
        Self { data, config }
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {

        let k = [   
            0x428a2f98u32, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
        ].into_iter().fold(vec![], |mut l, elem| {
            l.push(elem as u16);
            l.push((elem >> 16) as u16);
            l
        });

        let h = [
            0x6a09e667u32,
            0xbb67ae85,
            0x3c6ef372,
            0xa54ff53a,
            0x510e527f,
            0x9b05688c,
            0x1f83d9ab,
            0x5be0cd19
        ].into_iter().fold(vec![], |mut l, elem| {
            l.push(elem as u16);
            l.push((elem >> 16) as u16);
            l
        });
        
        let mut idx = 0;
        for input in self.data.inputs.iter() {

            let l: u64 = self.data.inputs[0].len() as u64;
        
            let coef = (l+1+8) / 64;
            let rem = (l+1+8) % 64;
            let size = coef * 64 + (rem > 0) as u64 * 64;
            let num_zeros = size - self.data.inputs[0].len() as u64 - 1 - 8;
            let mut copy = self.data.inputs[0].clone();
            copy.extend([0x80]);
            copy.extend(vec![0; num_zeros as usize]);
            copy.extend((l*8).to_be_bytes());
            let mut w: Vec<u16> = vec![];
            for i in 0..copy.len()/4 {
                w.push( copy[4*i+3] as u16 + (copy[4*i+2] as u16) * ( 1 << 8) );
                w.push( copy[4*i+1] as u16 + (copy[4*i+0] as u16) * ( 1 << 8) );
            }

            layouter.assign_region(
                || format!("Full SHA256 {}", idx), 
                |mut region| {
                    let k = k.clone();
                    let w = w.clone();
                    let h = h.clone();

                    let mut h_val = vec![];
                    let mut h_c = vec![];
                    for i in 0..w.len()/32 {
                        let mut w_p = vec![0; 32];
                        w_p.copy_from_slice(&w[32*i..32*(i+1)]);
                        let (w_val, w_c) = self.config.message_schedule_chip.load(&mut region, w_p, 2099 * i)?;
                        if i == 0 {
                            (h_val, h_c) = self.config.compression_chip.load(&mut region, w_c, w_val, k.clone(), h.clone(), 2099 * i + 547)?;
                        } else {
                            // let (w_val, w_c) = self.config.message_schedule_chip.load(&mut region, w_p, 2099 * (i+1))?;
                            (h_val, h_c) = self.config.compression_chip.load_steady(
                                &mut region, w_c, w_val, k.clone(), 
                                h_c, h_val, 2099 * i + 547
                            )?;
                        }
                    }
                    
                    Ok(())
                }
            )?;
            idx += 1;
        }

        Ok(())
    }
}

#[cfg(any(feature = "test", test))]
pub mod dev {
    use super::*;

    use ethers_core::types::H256;
    use halo2_proofs::{circuit::SimpleFloorPlanner, plonk::Circuit};
    use std::str::FromStr;

    lazy_static::lazy_static! {
        pub static ref INPUTS_OUTPUTS: (Vec<Vec<u8>>, Vec<H256>) = {
        [
            (
                "",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                "abc",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
            (
                "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
                "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
            ),
        ]
            .iter()
            .map(|(input, output)| {
                (
                    input.as_bytes().to_vec(),
                    H256::from_str(output).expect("SHA-256 hash is 32-bytes"),
                )
            })
            .unzip()
        };
    }

    #[derive(Default)]
    pub struct Sha2TestCircuit<F> {
        pub inputs: Vec<Vec<u8>>,
        pub outputs: Vec<H256>,
        pub _marker: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for Sha2TestCircuit<F> {
        type Config = Sha2Config<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let sha2_table = Sha2Table::construct(meta);
            Sha2Config::configure(meta, sha2_table)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.spread_table.load(&mut layouter)?;
            let chip = Sha2Chip::construct(
                config,
                Sha2Witness {
                    inputs: self.inputs.clone(),
                    _marker: PhantomData,
                },
            );
            chip.load(&mut layouter)?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
    use std::marker::PhantomData;

    use crate::dev::{Sha2TestCircuit, INPUTS_OUTPUTS};

    #[test]
    fn test_sha2_circuit() {
        let (inputs, outputs) = INPUTS_OUTPUTS.clone();

        let circuit: Sha2TestCircuit<Fr> = Sha2TestCircuit {
            inputs,
            outputs,
            _marker: PhantomData,
        };

        let k = 17;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        // prover.assert_satisfied();
        assert_eq!(prover.verify(), Ok(()));
    }
}
