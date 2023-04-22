use std::marker::PhantomData;
use crate::utils::create_interleave_num;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, TableColumn},
};

#[derive(Debug, Clone)]
pub(super) struct SpreadTableConfig<F: FieldExt, const NUM_BITS: usize> {
    pub(super) table: TableColumn,
    pub(super) tag: TableColumn,
    pub(super) spread: TableColumn,
    _marker: PhantomData<F>,
}

impl <F: FieldExt, const NUM_BITS: usize> SpreadTableConfig<F, NUM_BITS> {
    pub(super) fn configure(
        meta: &mut ConstraintSystem<F>
    ) -> Self {
        let tag = meta.lookup_table_column();
        let table = meta.lookup_table_column();
        let spread = meta.lookup_table_column();

        Self {
            table, 
            tag,
            spread,
            _marker: PhantomData
        }
    }


    pub(super) fn load(
        &self,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {

        layouter.assign_table(
            || "load spread table", 
            |mut table| {
                let mut tag = 0;
                let mut offset = 0;
                for i in 0..NUM_BITS {
                    // (2 ^ i) - 1 assignment
                    table.assign_cell(
                        || "Number Tag Beginner ", 
                        self.tag, 
                        offset, 
                        || Value::known(F::from(tag as u64))
                    )?;
                    table.assign_cell(
                        || "Number Table Beginner", 
                        self.table, 
                        offset, 
                        || Value::known(F::from((1<<i)-1 as u64))
                    )?;
                    table.assign_cell(
                        || "Number Spread Beginner", 
                        self.spread, 
                        offset, 
                        || Value::known(F::from(create_interleave_num((1<<i)-1) as u64))
                    )?;
                    offset += 1;
                    if i == 7 {
                        tag = 1;
                    } else if i == 10 {
                        tag = 2;
                    } else if i == 11 {
                        tag = 3;
                    } else if i == 13 {
                        tag = 4
                    } else if i == 14 {
                        tag = 5
                    }
                    for j in (1<<i)..((1<<i+1)-1) {
                        table.assign_cell(
                            || "Number Tag",
                            self.tag, 
                            offset, 
                            || Value::known(F::from(tag as u64))
                        )?;
                        table.assign_cell(
                            || "Number Table", 
                            self.table, 
                            offset, 
                            || Value::known(F::from(j as u64))
                        )?;
                        table.assign_cell(
                            || "Number Spread", 
                            self.spread, 
                            offset, 
                            || Value::known(F::from(create_interleave_num(j) as u64))
                        )?;
                        offset += 1;
                    }
                }
                table.assign_cell(
                    || "Number Tag",
                    self.tag, 
                    offset, 
                    || Value::known(F::from(5 as u64))
                )?;
                table.assign_cell(
                    || "Number Table", 
                    self.table, 
                    offset, 
                    || Value::known(F::from(((1<<NUM_BITS)-1) as u64))
                )?;
                table.assign_cell(
                    || "Number Spread", 
                    self.spread, 
                    offset, 
                    || Value::known(F::from(create_interleave_num((1<<NUM_BITS)-1) as u64))
                )?;
                Ok(())
            }
        )?;
        Ok(())
    }

}

#[cfg(test)]
mod tests {

    use super::*;
    // use crate::FieldExt;
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use halo2_proofs::plonk::{Column, Advice, Circuit};
    use halo2_proofs::poly::Rotation;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr as F};

    

    #[derive(Debug, Clone)]
    struct SpreadConfig<F: FieldExt, const NUM_BITS: usize> {
        input_tag: Column<Advice>,
        input_table: Column<Advice>,
        input_spread: Column<Advice>,
        table_config: SpreadTableConfig<F, NUM_BITS>,
    }

    impl<F: FieldExt, const NUM_BITS: usize> SpreadConfig<F, NUM_BITS> {
        fn configure(
            meta: &mut ConstraintSystem<F>
        ) -> Self {
            let input_tag = meta.advice_column();
            let input_table = meta.advice_column();
            let input_spread = meta.advice_column();
            let table_config = SpreadTableConfig::<F, NUM_BITS>::configure(meta);
            
            meta.lookup("Test Spread Table", |meta| {
                let it = meta.query_advice(input_tag, Rotation::cur());
                let ita = meta.query_advice(input_table, Rotation::cur());
                let is = meta.query_advice(input_spread, Rotation::cur());

                vec![
                    (it, table_config.tag),
                    (ita, table_config.table),
                    (is, table_config.spread),
                ]
            });

            Self {
                input_tag,
                input_spread,
                input_table,
                table_config
            }
        }

        pub fn assign(
            &self,
            mut layouter: impl Layouter<F>,
            tags: &Vec<Value<F>>,
            tables: &Vec<Value<F>>,
            spreads: &Vec<Value<F>>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "Assign Rows", 
                |mut region| {

                    for i in 0..tags.len() {
                        region.assign_advice(
                            || "tag", 
                            self.input_tag, 
                            i, 
                            || tags[i].clone()
                        )?;
                        region.assign_advice(
                            || "table", 
                            self.input_table, 
                            i, 
                            || tables[i].clone()
                        )?;
                        region.assign_advice(
                            || "spread", 
                            self.input_spread, 
                            i, 
                            || spreads[i].clone()
                        )?;
                    }
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[derive(Default, Clone)]
    struct SpreadCircuit<F: FieldExt, const NUM_BITS: usize> {
        tags: Vec<Value<F>>,
        tables: Vec<Value<F>>,
        spreads: Vec<Value<F>>,
    }

    impl<F: FieldExt, const NUM_BITS: usize> Circuit<F> for SpreadCircuit<F, NUM_BITS> {
        type Config = SpreadConfig<F, NUM_BITS>;
        type FloorPlanner = SimpleFloorPlanner;
        
        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            SpreadConfig::configure(meta)
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
            assert!(self.tags.len() == self.tables.len() && self.tables.len() == self.spreads.len());
            config.table_config.load(&mut layouter)?;
            config.assign(
                layouter.namespace(|| "Load Rows"), 
                &self.tags, 
                &self.tables, 
                &self.spreads
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_spread_table_circuit() {

        let raw_tags = vec![
            // smaller bit
            F::zero(), F::zero(), F::zero(), F::zero(), F::zero(), F::zero(), 
            // 7 bit
            F::zero(), F::one(), 
            // 10 bit
            F::one(), F::from(2),
            // 11 bit
            F::from(2), F::from(3),
            // 13 bit
            F::from(3), F::from(4),
            // 14 bit
            F::from(4), F::from(5),
        ];

        let raw_tables = vec![
            // smaller bit
            F::from(0b000), F::from(0b001), F::from(0b010), F::from(0b011), F::from(0b100), F::from(0b101), 
            // 7 bit
            F::from(0b1111111), F::from(0b10000000), 
            // 10 bit
            F::from(0b1111111111), F::from(0b10000000000),
            // 11 bit
            F::from(0b11111111111), F::from(0b100000000000),
            // 13 bit
            F::from(0b1111111111111), F::from(0b10000000000000),
            // 14 bit
            F::from(0b11111111111111), F::from(0b100000000000000),
        ];

        let raw_spreads = vec![
            // smaller bit
            F::from(0b000000), F::from(0b000001), F::from(0b000100), F::from(0b000101), F::from(0b010000), F::from(0b010001), 
            // 7 bit
            F::from(0b01010101010101), F::from(0b0100000000000000), 
            // 10 bit
            F::from(0b01010101010101010101), F::from(0b0100000000000000000000),
            // 11 bit
            F::from(0b0101010101010101010101), F::from(0b010000000000000000000000),
            // 13 bit
            F::from(0b01010101010101010101010101), F::from(0b0100000000000000000000000000),
            // 14 bit
            F::from(0b0101010101010101010101010101), F::from(0b010000000000000000000000000000),
        ];

        let tags: Vec<Value<F>> = raw_tags.iter().map(|elem| Value::known(*elem)).collect();
        let tables: Vec<Value<F>> = raw_tables.iter().map(|elem| Value::known(*elem)).collect();
        let spreads: Vec<Value<F>> = raw_spreads.iter().map(|elem| Value::known(*elem)).collect();

        let circuit = SpreadCircuit::<F, 16>{
            tags,
            tables,
            spreads,
        };

        let k = 17;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

    }



}