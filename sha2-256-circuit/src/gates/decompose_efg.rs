use std::marker::PhantomData;

use crate::utils::{
    create_range_2_check,
    create_spread_2_check,
    create_range_3_check,
    create_spread_3_check,
    create_value_4_check,
    create_interleave_num,
    create_tag,
};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};


#[derive(Debug, Clone)]
pub struct DecomposeEFGConfig<F: FieldExt> {
    pub s_efg: Selector,
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    a6: Column<Advice>,
    a7: Column<Advice>,
    a8: Column<Advice>,
    _marker: PhantomData<F>
}


impl<F: FieldExt> DecomposeEFGConfig<F> {

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
    ) -> Self {
        let s_efg = meta.complex_selector();

        meta.create_gate(
            "Decompose EFG", 
            |meta| {
                let s_efg = meta.query_selector(s_efg);

                let d_tag = meta.query_advice(a0, Rotation::cur());
                let c_tag = meta.query_advice(a0, Rotation::next());

                let b_lo = meta.query_advice(a3, Rotation::cur());
                let s_b_lo = meta.query_advice(a4, Rotation::cur());

                let b_hi = meta.query_advice(a5, Rotation::cur());
                let s_b_hi = meta.query_advice(a6, Rotation::cur());

                let a_lo = meta.query_advice(a3, Rotation::next());
                let s_a_lo = meta.query_advice(a4, Rotation::next());

                let a_hi = meta.query_advice(a5, Rotation::next());
                let s_a_hi = meta.query_advice(a6, Rotation::next());

                let lo = meta.query_advice(a7, Rotation::cur());
                // let s_lo = meta.query_advice(a8, Rotation::cur());

                let hi = meta.query_advice(a7, Rotation::next());
                // let s_hi = meta.query_advice(a8, Rotation::next());

                let tag_constraint = d_tag + create_value_4_check(c_tag);

                let b_lo_constraint = create_range_2_check(b_lo.clone());
                let s_b_lo_constraint = create_spread_2_check(b_lo.clone(), s_b_lo);
                
                let a_lo_constraint = create_range_3_check(a_lo.clone());
                let s_a_lo_constraint = create_spread_3_check(a_lo.clone(), s_a_lo);

                let a_hi_constraint = create_range_3_check(a_hi.clone());
                let s_a_hi_constraint = create_spread_3_check(a_hi.clone(), s_a_hi);

                let b_hi_constraint = create_range_3_check(b_hi.clone());
                let s_b_hi_constraint = create_spread_3_check(b_hi.clone(), s_b_hi);

                let d = meta.query_advice(a1, Rotation::cur());
                let c = meta.query_advice(a1, Rotation::next());
                let decompose_constraint = 
                    a_lo +
                    Expression::Constant(F::from(1 << 3)) * a_hi + 
                    Expression::Constant(F::from(1 << 6)) * b_lo + 
                    Expression::Constant(F::from(1 << 8)) * b_hi + 
                    Expression::Constant(F::from(1 << 11)) * c + 
                    Expression::Constant(F::from(1 << 25)) * d -  
                    Expression::Constant(F::from(1 << 16)) * hi - lo;

                vec![
                    s_efg * 
                    (
                        tag_constraint +
                        decompose_constraint +
                        b_lo_constraint +
                        s_b_lo_constraint +
                        a_lo_constraint +
                        s_a_lo_constraint +
                        a_hi_constraint +
                        s_a_hi_constraint +
                        b_hi_constraint +
                        s_b_hi_constraint 
                    ),
                ]
            } 
        );
        Self {
            s_efg,
            a0, a1, a2, a3, a4, a5, a6, a7, a8,
            _marker: PhantomData
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        e_lo: u16,
        e_hi: u16,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        let e: u32 = e_lo as u32 + e_hi as u32 * (1 << 16);
        let e_a = e & 0b111111;
        let e_b = (e >> 6) & 0b11111;
        let e_c = (e >> 11) & 0x3FFF;
        let e_d = e >> 25;

        let e_a_lo = e_a & 0b111;
        let e_a_hi = e_a >> 3;
        let e_b_lo = e_b & 0b11;
        let e_b_hi = e_b >> 2;

        self.s_efg.enable(region, offset)?;

        region.assign_advice(|| "sd_efg d tag", self.a0, offset, || Value::known(F::from(create_tag(e_d as u16) as u64)))?;
        region.assign_advice(|| "sd_efg d", self.a1, offset, || Value::known(F::from(e_d as u64)))?;
        let s_d = region.assign_advice(|| "sd_efg s_d", self.a2, offset, || Value::known(F::from(create_interleave_num(e_d) as u64)))?;

        region.assign_advice(|| "sd_efg b_lo", self.a3, offset, || Value::known(F::from(e_b_lo as u64)))?;
        let s_b_lo = region.assign_advice(|| "sd_efg s_b_lo", self.a4, offset, || Value::known(F::from(create_interleave_num(e_b_lo) as u64)))?;

        region.assign_advice(|| "sd_efg b_hi", self.a5, offset, || Value::known(F::from(e_b_hi as u64)))?;
        let s_b_hi = region.assign_advice(|| "sd_efg s_b_hi", self.a6, offset, || Value::known(F::from(create_interleave_num(e_b_hi) as u64)))?;

        let e_lo_c = region.assign_advice(|| "sd_efg e_lo", self.a7, offset, || Value::known(F::from(e_lo as u64)))?;
        let s_e_lo =region.assign_advice(|| "sd_efg s_e_lo", self.a8, offset, || Value::known(F::from(create_interleave_num(e_lo as u32) as u64)))?;

        region.assign_advice(|| "sd_efg c tag", self.a0, offset+1, || Value::known(F::from(create_tag(e_c as u16) as u64)))?;
        region.assign_advice(|| "sd_efg c", self.a1, offset+1, || Value::known(F::from(e_c as u64)))?;
        let s_c = region.assign_advice(|| "sd_efg s_c", self.a2, offset+1, || Value::known(F::from(create_interleave_num(e_c) as u64)))?;

        region.assign_advice(|| "sd_efg a_lo", self.a3, offset+1, || Value::known(F::from(e_a_lo as u64)))?;
        let s_a_lo = region.assign_advice(|| "sd_efg s_a_lo", self.a4, offset+1, || Value::known(F::from(create_interleave_num(e_a_lo) as u64)))?;

        region.assign_advice(|| "sd_efg b_hi", self.a5, offset+1, || Value::known(F::from(e_a_hi as u64)))?;
        let s_a_hi = region.assign_advice(|| "sd_efg s_b_hi", self.a6, offset+1, || Value::known(F::from(create_interleave_num(e_a_hi) as u64)))?;

        let e_hi_c = region.assign_advice(|| "sd_efg e_hi", self.a7, offset+1, || Value::known(F::from(e_hi as u64)))?;
        let s_e_hi = region.assign_advice(|| "sd_efg s_e_hi", self.a8, offset+1, || Value::known(F::from(create_interleave_num(e_hi as u32) as u64)))?;
        
        let res = vec![s_a_lo, s_a_hi, s_b_lo, s_b_hi, s_c, s_d, s_e_lo, s_e_hi, e_lo_c, e_hi_c];

        Ok(res)
    }

    pub fn assign_steady(
        &self,
        region: &mut Region<F>,
        e_lo: u16,
        e_hi: u16,
        e_lo_c: AssignedCell<F, F>,
        e_hi_c: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        let e: u32 = e_lo as u32 + e_hi as u32 * (1 << 16);
        let e_a = e & 0b111111;
        let e_b = (e >> 6) & 0b11111;
        let e_c = (e >> 11) & 0x3FFF;
        let e_d = e >> 25;

        let e_a_lo = e_a & 0b111;
        let e_a_hi = e_a >> 3;
        let e_b_lo = e_b & 0b11;
        let e_b_hi = e_b >> 2;

        self.s_efg.enable(region, offset)?;

        region.assign_advice(|| "sd_efg d tag", self.a0, offset, || Value::known(F::from(create_tag(e_d as u16) as u64)))?;
        region.assign_advice(|| "sd_efg d", self.a1, offset, || Value::known(F::from(e_d as u64)))?;
        let s_d = region.assign_advice(|| "sd_efg s_d", self.a2, offset, || Value::known(F::from(create_interleave_num(e_d) as u64)))?;

        region.assign_advice(|| "sd_efg b_lo", self.a3, offset, || Value::known(F::from(e_b_lo as u64)))?;
        let s_b_lo = region.assign_advice(|| "sd_efg s_b_lo", self.a4, offset, || Value::known(F::from(create_interleave_num(e_b_lo) as u64)))?;

        region.assign_advice(|| "sd_efg b_hi", self.a5, offset, || Value::known(F::from(e_b_hi as u64)))?;
        let s_b_hi = region.assign_advice(|| "sd_efg s_b_hi", self.a6, offset, || Value::known(F::from(create_interleave_num(e_b_hi) as u64)))?;

        let e_lo_c_2 = e_lo_c.copy_advice(|| "sd_efg e_lo", region, self.a7, offset)?;
        let s_e_lo =region.assign_advice(|| "sd_efg s_e_lo", self.a8, offset, || Value::known(F::from(create_interleave_num(e_lo as u32) as u64)))?;

        region.assign_advice(|| "sd_efg c tag", self.a0, offset+1, || Value::known(F::from(create_tag(e_c as u16) as u64)))?;
        region.assign_advice(|| "sd_efg c", self.a1, offset+1, || Value::known(F::from(e_c as u64)))?;
        let s_c = region.assign_advice(|| "sd_efg s_c", self.a2, offset+1, || Value::known(F::from(create_interleave_num(e_c) as u64)))?;

        region.assign_advice(|| "sd_efg a_lo", self.a3, offset+1, || Value::known(F::from(e_a_lo as u64)))?;
        let s_a_lo = region.assign_advice(|| "sd_efg s_a_lo", self.a4, offset+1, || Value::known(F::from(create_interleave_num(e_a_lo) as u64)))?;

        region.assign_advice(|| "sd_efg b_hi", self.a5, offset+1, || Value::known(F::from(e_a_hi as u64)))?;
        let s_a_hi = region.assign_advice(|| "sd_efg s_b_hi", self.a6, offset+1, || Value::known(F::from(create_interleave_num(e_a_hi) as u64)))?;

        let e_hi_c_2 = e_hi_c.copy_advice(|| "sd_efg e_hi", region, self.a7, offset+1)?;
        let s_e_hi = region.assign_advice(|| "sd_efg s_e_hi", self.a8, offset+1, || Value::known(F::from(create_interleave_num(e_hi as u32) as u64)))?;
        
        let res = vec![s_a_lo, s_a_hi, s_b_lo, s_b_hi, s_c, s_d, s_e_lo, s_e_hi, e_lo_c_2, e_hi_c_2];

        Ok(res)
    }

}

