use std::marker::PhantomData;

use crate::utils::{
    create_range_2_check,
    create_spread_2_check,
    create_range_3_check,
    create_spread_3_check,
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
pub struct DecomposeABCConfig<F: FieldExt> {
    pub s_abc: Selector,
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


impl<F: FieldExt> DecomposeABCConfig<F> {

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
        let s_abc = meta.complex_selector();

        meta.create_gate(
            "Decompose ABC", 
            |meta| {
                let s_abc = meta.query_selector(s_abc);

                let b_tag = meta.query_advice(a0, Rotation::cur());
                let d_tag = meta.query_advice(a0, Rotation::next());

                let c_lo = meta.query_advice(a3, Rotation::cur());
                let s_c_lo = meta.query_advice(a4, Rotation::cur());

                let c_mi = meta.query_advice(a5, Rotation::cur());
                let s_c_mi = meta.query_advice(a6, Rotation::cur());

                let a = meta.query_advice(a3, Rotation::next());
                let s_a = meta.query_advice(a4, Rotation::next());

                let c_hi = meta.query_advice(a5, Rotation::next());
                let s_c_hi = meta.query_advice(a6, Rotation::next());

                let lo = meta.query_advice(a7, Rotation::cur());
                // let s_lo = meta.query_advice(a8, Rotation::cur());

                let hi = meta.query_advice(a7, Rotation::next());
                // let s_hi = meta.query_advice(a8, Rotation::next());

                let b_tag_constraint = b_tag.clone() * (b_tag.clone()-Expression::Constant(F::one())) * (b_tag-Expression::Constant(F::from(2)));
                let d_tag_constraint = d_tag.clone() * (d_tag-Expression::Constant(F::one()));

                let a_constraint = create_range_2_check(a.clone());
                let s_a_constraint = create_spread_2_check(a.clone(), s_a);
                
                let c_lo_constraint = create_range_3_check(c_lo.clone());
                let s_c_lo_constraint = create_spread_3_check(c_lo.clone(), s_c_lo);

                let c_mi_constraint = create_range_3_check(c_mi.clone());
                let s_c_mi_constraint = create_spread_3_check(c_mi.clone(), s_c_mi);

                let c_hi_constraint = create_range_3_check(c_hi.clone());
                let s_c_hi_constraint = create_spread_3_check(c_hi.clone(), s_c_hi);

                let b = meta.query_advice(a1, Rotation::cur());
                let d = meta.query_advice(a1, Rotation::next());
                let decompose_constraint = 
                    a +
                    Expression::Constant(F::from(1 << 2)) * b + 
                    Expression::Constant(F::from(1 << 13)) * c_lo + 
                    Expression::Constant(F::from(1 << 16)) * c_mi + 
                    Expression::Constant(F::from(1 << 19)) * c_hi + 
                    Expression::Constant(F::from(1 << 22)) * d -  
                    Expression::Constant(F::from(1 << 16)) * hi - lo;

                vec![
                    s_abc * 
                    (   
                        b_tag_constraint + 
                        d_tag_constraint +
                        a_constraint +
                        s_a_constraint +
                        c_lo_constraint + 
                        s_c_lo_constraint +
                        c_mi_constraint + 
                        s_c_mi_constraint +
                        c_hi_constraint +
                        s_c_hi_constraint + 
                        decompose_constraint
                    )
                ]
            } 
        );
        Self {
            s_abc,
            a0, a1, a2, a3, a4, a5, a6, a7, a8,
            _marker: PhantomData
        }

    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        a_lo: u16,
        a_hi: u16,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        let a = a_lo as u32 + a_hi as u32 * ( 1<<16 );
        let a_a = a & 0b11;
        let a_b = (a >> 2) & 0x7FF;
        let a_c = ( a >> 13) & 0x1FF;
        let a_d = a >> 22;

        let a_c_lo = a_c & 0b111;
        let a_c_mi = (a_c>>3) & 0b111;
        let a_c_hi = a_c >> 6;

        self.s_abc.enable(region, offset)?;

        region.assign_advice(|| "sd_abc b tag", self.a0, offset, || Value::known(F::from(create_tag(a_b as u16) as u64)))?;
        region.assign_advice(|| "sd_abc b", self.a1, offset, || Value::known(F::from(a_b as u64)))?;
        let s_b = region.assign_advice(|| "sd_abc s_b", self.a2, offset, || Value::known(F::from(create_interleave_num(a_b) as u64)))?;

        region.assign_advice(|| "sd_abc c_lo", self.a3, offset, || Value::known(F::from(a_c_lo as u64)))?;
        let s_c_lo = region.assign_advice(|| "sd_abc s_c_lo", self.a4, offset, || Value::known(F::from(create_interleave_num(a_c_lo) as u64)))?;

        region.assign_advice(|| "sd_abc c_mi", self.a5, offset, || Value::known(F::from(a_c_mi as u64)))?;
        let s_c_mi = region.assign_advice(|| "sd_abc s_b_hi", self.a6, offset, || Value::known(F::from(create_interleave_num(a_c_mi) as u64)))?;

        let a_lo_c = region.assign_advice(|| "sd_abc a_lo", self.a7, offset, || Value::known(F::from(a_lo as u64)))?;
        let s_a_lo = region.assign_advice(|| "sd_abc s_a_lo", self.a8, offset, || Value::known(F::from(create_interleave_num(a_lo as u32) as u64)))?;

        region.assign_advice(|| "sd_abc d tag", self.a0, offset+1, || Value::known(F::from(create_tag(a_d as u16) as u64)))?;
        region.assign_advice(|| "sd_abc d", self.a1, offset+1, || Value::known(F::from(a_d as u64)))?;
        let s_d = region.assign_advice(|| "sd_abc s_d", self.a2, offset+1, || Value::known(F::from(create_interleave_num(a_d) as u64)))?;

        region.assign_advice(|| "sd_abc a", self.a3, offset+1, || Value::known(F::from(a_a as u64)))?;
        let s_a = region.assign_advice(|| "sd_abc s_a", self.a4, offset+1, || Value::known(F::from(create_interleave_num(a_a) as u64)))?;

        region.assign_advice(|| "sd_abc c_hi", self.a5, offset+1, || Value::known(F::from(a_c_hi as u64)))?;
        let s_c_hi = region.assign_advice(|| "sd_abc s_c_hi", self.a6, offset+1, || Value::known(F::from(create_interleave_num(a_c_hi) as u64)))?;

        let a_hi_c = region.assign_advice(|| "sd_abc a_hi", self.a7, offset+1, || Value::known(F::from(a_hi as u64)))?;
        let s_a_hi = region.assign_advice(|| "sd_abc s_a_hi", self.a8, offset+1, || Value::known(F::from(create_interleave_num(a_hi as u32) as u64)))?;

        let res = vec![s_a, s_b, s_c_lo, s_c_mi, s_c_hi, s_d, s_a_lo, s_a_hi, a_lo_c, a_hi_c];
        Ok(res)
    }


    pub fn assign_steady(
        &self,
        region: &mut Region<F>,
        a_lo: u16,
        a_hi: u16,
        a_lo_c: AssignedCell<F, F>,
        a_hi_c: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        let a = a_lo as u32 + a_hi as u32 * ( 1<<16 );
        let a_a = a & 0b11;
        let a_b = (a >> 2) & 0x7FF;
        let a_c = ( a >> 13) & 0x1FF;
        let a_d = a >> 22;

        let a_c_lo = a_c & 0b111;
        let a_c_mi = (a_c>>3) & 0b111;
        let a_c_hi = a_c >> 6;

        self.s_abc.enable(region, offset)?;

        region.assign_advice(|| "sd_abc b tag", self.a0, offset, || Value::known(F::from(create_tag(a_b as u16) as u64)))?;
        region.assign_advice(|| "sd_abc b", self.a1, offset, || Value::known(F::from(a_b as u64)))?;
        let s_b = region.assign_advice(|| "sd_abc s_b", self.a2, offset, || Value::known(F::from(create_interleave_num(a_b) as u64)))?;

        region.assign_advice(|| "sd_abc c_lo", self.a3, offset, || Value::known(F::from(a_c_lo as u64)))?;
        let s_c_lo = region.assign_advice(|| "sd_abc s_c_lo", self.a4, offset, || Value::known(F::from(create_interleave_num(a_c_lo) as u64)))?;

        region.assign_advice(|| "sd_abc c_mi", self.a5, offset, || Value::known(F::from(a_c_mi as u64)))?;
        let s_c_mi = region.assign_advice(|| "sd_abc s_b_hi", self.a6, offset, || Value::known(F::from(create_interleave_num(a_c_mi) as u64)))?;

        let a_lo_c_2 = a_lo_c.copy_advice(|| "sd_abc a_lo", region, self.a7, offset)?;
        let s_a_lo = region.assign_advice(|| "sd_abc s_a_lo", self.a8, offset, || Value::known(F::from(create_interleave_num(a_lo as u32) as u64)))?;

        region.assign_advice(|| "sd_abc d tag", self.a0, offset+1, || Value::known(F::from(create_tag(a_d as u16) as u64)))?;
        region.assign_advice(|| "sd_abc d", self.a1, offset+1, || Value::known(F::from(a_d as u64)))?;
        let s_d = region.assign_advice(|| "sd_abc s_d", self.a2, offset+1, || Value::known(F::from(create_interleave_num(a_d) as u64)))?;

        region.assign_advice(|| "sd_abc a", self.a3, offset+1, || Value::known(F::from(a_a as u64)))?;
        let s_a = region.assign_advice(|| "sd_abc s_a", self.a4, offset+1, || Value::known(F::from(create_interleave_num(a_a) as u64)))?;

        region.assign_advice(|| "sd_abc c_hi", self.a5, offset+1, || Value::known(F::from(a_c_hi as u64)))?;
        let s_c_hi = region.assign_advice(|| "sd_abc s_c_hi", self.a6, offset+1, || Value::known(F::from(create_interleave_num(a_c_hi) as u64)))?;

        let a_hi_c_2 = a_hi_c.copy_advice(|| "sd_abc a_hi", region, self.a7, offset+1)?;
        let s_a_hi = region.assign_advice(|| "sd_abc s_a_hi", self.a8, offset+1, || Value::known(F::from(create_interleave_num(a_hi as u32) as u64)))?;

        let res = vec![s_a, s_b, s_c_lo, s_c_mi, s_c_hi, s_d, s_a_lo, s_a_hi, a_lo_c_2, a_hi_c_2];
        Ok(res)
    }

}

