use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};

use crate::utils::{create_interleave_num, create_tag};


#[derive(Debug, Clone)]
pub struct DecomposeThreeConfig<F: FieldExt> {
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    s_three: Selector,
    _marker: PhantomData<F>
}


impl<F: FieldExt> DecomposeThreeConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_three = meta.selector();

        meta.create_gate(
            "Decompose One", 
            |meta| {
                let s_three = meta.query_selector(s_three);

                let w_d = meta.query_advice(a1, Rotation::cur());
                let w_a = meta.query_advice(a1, Rotation::next());
                let w_c = meta.query_advice(a3, Rotation::next());
                let w_b = meta.query_advice(a4, Rotation::next());

                let w = meta.query_advice(a5, Rotation::cur());

                let decompose_constraint = 
                    w_a +
                    w_b * Expression::Constant(F::from(1 << 10)) +
                    w_c * Expression::Constant(F::from(1 << 17)) +
                    w_d * Expression::Constant(F::from(1 << 19)) -
                    w;

                vec![
                    s_three * decompose_constraint
                ]
            }
        );
        Self {
            a0, a1, a2, a3, a4,
            s_three,
            _marker: PhantomData
        }

    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        w_lo: u16,
        w_hi: u16,
        offset: usize,
    ) -> Result<(Vec<AssignedCell<F, F>>, u32, u32), Error> {

        let w = w_lo as u32 + (w_hi as u32) * (1<<16);
        let w_a = w & 0b1111111111;
        let w_b = ( w >> 10 ) & 0b1111111;
        let w_c = ( w >> 17 ) & 0b11;
        let w_d = w >> 19;
        region.assign_advice(|| "sd3 wd tag", self.a0, offset, || Value::known(F::from(create_tag(w_d as u16))))?;
        region.assign_advice(|| "sd3 wd", self.a1, offset, || Value::known(F::from(w_d as u64)))?;
        let s_d = region.assign_advice(|| "sd3 wd spread", self.a2, offset, || Value::known(F::from(create_interleave_num(w_d) as u64)))?;

        region.assign_advice(|| "sd3 wa tag", self.a0, offset+1, || Value::known(F::from(create_tag(w_a as u16))))?;
        region.assign_advice(|| "sd3 wa", self.a1, offset+1, || Value::known(F::from(w_a as u64)))?;
        let s_a = region.assign_advice(|| "sd3 wa spread", self.a2, offset+1, || Value::known(F::from(create_interleave_num(w_a) as u64)))?;

        let c = region.assign_advice(|| "sd3 wc", self.a3, offset+1, || Value::known(F::from(w_c as u64)))?;
        let b = region.assign_advice(|| "sd3 wb", self.a4, offset+1, || Value::known(F::from(w_b as u64)))?;
        let res = vec![s_d, s_a, c, b];
        Ok((res, w_b, w_c))
    }

}

