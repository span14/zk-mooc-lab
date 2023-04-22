use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error},
};

use crate::gates::{
    decompose_zero::DecomposeZeroConfig,
    decompose_one::DecomposeOneConfig,
    decompose_two::DecomposeTwoConfig,
    decompose_three::DecomposeThreeConfig,
    w_new::WNewConfig,
    sigma_zero_v_one::Sigma0V1Config,
    sigma_zero_v_two::Sigma0V2Config,
    sigma_one_v_one::Sigma1V1Config,
    sigma_one_v_two::Sigma1V2Config,
};
use crate::utils::{sigma0_r, sigma1_r};

#[derive(Debug, Clone)]
pub struct MessageScheduleChip<F: FieldExt> {
    sd0: DecomposeZeroConfig<F>,
    sd1: DecomposeOneConfig<F>,
    sd2: DecomposeTwoConfig<F>,
    sd3: DecomposeThreeConfig<F>,
    sw: WNewConfig<F>,
    ss0v1: Sigma0V1Config<F>,
    ss0v2: Sigma0V2Config<F>,
    ss1v1: Sigma1V1Config<F>,
    ss1v2: Sigma1V2Config<F>,
}

impl<F: FieldExt> MessageScheduleChip<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
        a6: Column<Advice>,
        a7: Column<Advice>,
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let sd0 = DecomposeZeroConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let sd1 = DecomposeOneConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let sd2 = DecomposeTwoConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let sd3 = DecomposeThreeConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let sw = WNewConfig::configure(meta, a5, a6, a7, a8, a9);
        let ss0v1 = Sigma0V1Config::configure(meta, a0, a1, a2, a3, a4, a5, a6);
        let ss0v2 = Sigma0V2Config::configure(meta, a0, a1, a2, a3, a4, a5, a6, a7);
        let ss1v1 = Sigma1V1Config::configure(meta, a0, a1, a2, a3, a4, a5, a6);
        let ss1v2 = Sigma1V2Config::configure(meta, a0, a1, a2, a3, a4, a5, a6, a7);

        Self {
            sd0,
            sd1,
            sd2,
            sd3,
            sw,
            ss0v1,
            ss0v2,
            ss1v1,
            ss1v2,
        }
    }

    pub fn load(
        &self,
        region: &mut Region<F>,
        w: Vec<u16>,
        offset: usize,
    ) -> Result<(Vec<u16>, Vec<AssignedCell<F, F>>), Error> {
        let mut res = vec![];
        let mut w_all: Vec<u16> = w.clone();
        let mut w_i: Vec<AssignedCell<F, F>> = vec![];
        let mut s0_w_i_15: Vec<AssignedCell<F, F>> = vec![];
        let mut s1_w_i_2: Vec<AssignedCell<F, F>> = vec![];
        // Input W0 and W16 Computation
        let mut w_cell = self.sd0.assign_special_0(region, w_all[0], w_all[1], offset)?;
        res.extend_from_slice(&w_cell);
        let (r1, w16) = self.sw.assign(
            region, w_all[0], w_all[1], w_all[2], w_all[3], 
            w_all[18], w_all[19], w_all[28], w_all[29], offset+1
        )?;
        w_i.push(r1[0].clone());
        s0_w_i_15.push(r1[1].clone());
        s0_w_i_15.push(r1[2].clone());
        s1_w_i_2.push(r1[3].clone());
        s1_w_i_2.push(r1[4].clone());
        w_all.push((w16 & 0xFFFF) as u16);
        w_all.push((w16 >> 16) as u16);
        // Input W1..13 and W17..29 Computation
        for i in 0..13 {
            w_cell = self.sd0.assign(region, w_all[2*(i+1)], w_all[2*(i+1)+1], offset+6*i+2)?;
            res.extend_from_slice(&w_cell);
            let (temp, a, b) = self.sd1.assign(region, w_all[2*(i+1)], w_all[2*(i+1)+1], offset+6*i+2)?;
            let (r_lo, r_hi) = sigma0_r(w_all[2*(i+1)], w_all[2*(i+1)+1]);
            self.ss0v1.assign(region, r_lo, r_hi, 
                temp[1].clone(), temp[0].clone(), 
                temp[2].clone(), temp[3].clone(), 
                s0_w_i_15[2*i].clone(), 
                s0_w_i_15[2*i+1].clone(), 
                b as u16, a as u16, offset+6*i+2+3
            )?;
            let (res, w_n) = self.sw.assign(
                region, 
                w_all[2*(i+1)], w_all[2*(i+1)+1], 
                w_all[2*(i+2)], w_all[2*(i+2)+1], 
                w_all[2*(i+10)], w_all[2*(i+10)+1], 
                w_all[2*(i+15)], w_all[2*(i+15)+1],
                offset+6*i+2+1
            )?;
            w_i.push(res[0].clone());
            s0_w_i_15.push(res[1].clone());
            s0_w_i_15.push(res[2].clone());
            s1_w_i_2.push(res[3].clone());
            s1_w_i_2.push(res[4].clone());
            w_all.push((w_n & 0xFFFF) as u16);
            w_all.push((w_n >> 16) as u16);
        }
        // Input W14..48 and W30..64
        for i in 0..35 {
            if i < 2 {
                w_cell = self.sd0.assign(
                    region, 
                    w_all[2*(i+14)], w_all[2*(i+14)+1],
                    offset+11*i + 80 + 1
                )?;
                res.extend_from_slice(&w_cell);
            } else {
                w_cell = self.sd0.assign_special_3(
                    region, w_all[2*(i+14)], w_all[2*(i+14)+1], 
                    w_i[i-2].clone(),
                    offset+11*i + 80 + 1
                )?;
                res.extend_from_slice(&w_cell);
            }

            let (temp, a, b, c, e, f) = self.sd2.assign(region, w_all[2*(i+14)], w_all[2*(i+14)+1], offset+11*i + 80 + 1)?;
            let (r_lo, r_hi) = sigma0_r(w_all[2*(i+14)], w_all[2*(i+14)+1]);
            let (r_lo_1, r_hi_1) = sigma1_r(w_all[2*(i+14)], w_all[2*(i+14)+1]);
            let temp1 = self.ss0v2.assign(
                region, r_lo, r_hi, 
                temp[1].clone(), temp[0].clone(), temp[2].clone(), b as u16, temp[3].clone(), a as u16, temp[4].clone(), 
                c as u16, e as u16, f as u16, 
                s0_w_i_15[2*(i+13)].clone(), s0_w_i_15[2*(i+13)+1].clone(), 
                offset+11*i + 80 + 4
            )?;
            self.ss1v2.assign(
                region, r_lo_1, r_hi_1, 
                temp1[0].clone(), temp1[1].clone(), temp[2].clone(), b as u16, temp[3].clone(), a as u16, temp[4].clone(),
                c as u16, e as u16, f as u16, 
                s1_w_i_2[2*i].clone(), s1_w_i_2[2*i+1].clone(),
                offset+11*i + 80 + 8
            )?;
            let (res, w_n) = self.sw.assign(
                region, 
                w_all[2*(i+14)], w_all[2*(i+14)+1], 
                w_all[2*(i+15)], w_all[2*(i+15)+1], 
                w_all[2*(i+23)], w_all[2*(i+23)+1], 
                w_all[2*(i+28)], w_all[2*(i+28)+1],
                offset+11*i + 80 + 2
            )?;
            w_i.push(res[0].clone());
            s0_w_i_15.push(res[1].clone());
            s0_w_i_15.push(res[2].clone());
            s1_w_i_2.push(res[3].clone());
            s1_w_i_2.push(res[4].clone());
            w_all.push((w_n & 0xFFFF) as u16);
            w_all.push((w_n >> 16) as u16);
        }

        // Input W49..61
        for i in 0..13 {
            w_cell = self.sd0.assign_special_3(
                region, w_all[2*(i+49)], w_all[2*(i+49)+1],
                w_i[i+33].clone(),
                offset+6*i + 465
            )?;
            res.extend_from_slice(&w_cell);
            let (r_lo, r_hi) = sigma1_r(w_all[2*(i+49)], w_all[2*(i+49)+1]);
            let (temp, b, c) = self.sd3.assign(
                region, 
                w_all[2*(i + 49)], w_all[2*(i+49)+1],
                offset+6*i + 465
            )?;
            self.ss1v1.assign(
                region, 
                r_lo, r_hi, 
                temp[1].clone(), temp[0].clone(), temp[3].clone(), b as u16, c as u16,
                temp[2].clone(), s1_w_i_2[2*(i+35)].clone(), s1_w_i_2[2*(i+35)+1].clone(), 
                offset+6*i + 465 + 3
            )?;
        }

        // Input W62..63
        w_cell = self.sd0.assign_special_3(
            region, w_all[2*62], w_all[2*62+1],
            w_i[46].clone(),
            offset+543
        )?;
        res.extend_from_slice(&w_cell);
        w_cell = self.sd0.assign_special_3(
            region, w_all[2*63], w_all[2*63+1], 
            w_i[47].clone(),
            offset+545
        )?;
        res.extend_from_slice(&w_cell);

        Ok((w_all, res))
    }

}

#[cfg(test)]
mod tests {

    use super::*;
    use std::marker::PhantomData;
    use crate::spread_table::SpreadTableConfig;
    use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner};
    use halo2_proofs::plonk::{Column, Advice, Circuit};
    use halo2_proofs::poly::Rotation;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr as F};


    #[derive(Debug, Clone)]
    struct MessageScheduleConfig<F: FieldExt, const NUM_BITS: usize> {
        message_schedule_chip: MessageScheduleChip<F>,
        table_config: SpreadTableConfig<F, NUM_BITS>,
    }
    
    impl<F: FieldExt, const NUM_BITS: usize> MessageScheduleConfig<F, NUM_BITS> {
        fn configure(
            meta: &mut ConstraintSystem<F>
        ) -> Self {
            let mut cols: Vec<Column<Advice>> = vec![];
            for i in 0..10 {
                cols.push(meta.advice_column());
                meta.enable_equality(cols[i]);
            }
            let table_config = SpreadTableConfig::configure(meta);
            let message_schedule_chip = MessageScheduleChip::configure(
                meta, 
                cols[0], cols[1], cols[2], cols[3], cols[4], 
                cols[5], cols[6], cols[7], cols[8], cols[9]
            );

            meta.lookup("Spread Table", |meta| {
                let it = meta.query_advice(cols[0], Rotation::cur());
                let ita = meta.query_advice(cols[1], Rotation::cur());
                let is = meta.query_advice(cols[2], Rotation::cur());

                vec![
                    (it, table_config.tag),
                    (ita, table_config.table),
                    (is, table_config.spread),
                ]
            });


            Self {
                table_config,
                message_schedule_chip
            }

        }

        pub fn assign(
            &self,
            mut layouter: impl Layouter<F>,
            w: Vec<u16>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "Message Schedule", 
                |mut region| {
                    let w = w.clone();
                    self.message_schedule_chip.load(&mut region, w, 0)?;
                    Ok(())
                }
            )?;
            Ok(())
        }
    }

    #[derive(Default, Clone)]
    struct MessageScheduleCircuit<F: FieldExt, const NUM_BITS: usize> {
        w: Vec<u16>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt, const NUM_BITS: usize> Circuit<F> for MessageScheduleCircuit<F, NUM_BITS> {
        type Config = MessageScheduleConfig<F, NUM_BITS>;
        type FloorPlanner = SimpleFloorPlanner;
        
        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            MessageScheduleConfig::configure(meta)
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
            config.table_config.load(&mut layouter)?;
            config.assign(
                layouter.namespace(|| "Load Message Schedules"), 
                self.w.clone(),
            )?;
            Ok(())
        }
    }

    #[test]
    fn test_message_schedule_circuit() {
        let mut input: Vec<u8> = "abc".as_bytes().to_vec();
        let l: u64 = input.len() as u64 * 8;
        
        let coef = ((input.len() * 8 + 1 + 64) - (input.len() * 8 + 1 + 64).rem_euclid(512))/512;
        let size = (coef+1) * 64;
        let num_zeros = size - input.len() - 9;
        
        input.extend([0x80]);
        input.extend(vec![0; num_zeros]);
        input.extend(l.to_be_bytes());
        let mut w: Vec<u16> = vec![];
        for i in 0..input.len()/2 {
            w.push( input[2*i] as u16 + (input[2*i+1] as u16) * ( 1 << 8) );
        }

        let circuit = MessageScheduleCircuit::<F, 16> {
            w,
            _marker: PhantomData
        };
        
        let k = 17;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        

    }


}