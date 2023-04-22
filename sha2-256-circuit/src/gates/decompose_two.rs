use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};
use crate::utils::{create_interleave_num, create_tag};

#[derive(Debug, Clone)]
pub struct DecomposeTwoConfig<F: FieldExt> {
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    s_two: Selector,
    _marker: PhantomData<F>
}


impl<F: FieldExt> DecomposeTwoConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_two = meta.selector();

        meta.create_gate(
            "Decompose Two", 
            |meta| {
                let s_two = meta.query_selector(s_two);

                let w_g = meta.query_advice(a1, Rotation::prev());
                let w_d = meta.query_advice(a1, Rotation::cur());
                let w_b = meta.query_advice(a1, Rotation::next());
                let w_a = meta.query_advice(a3, Rotation::prev());
                let w_e = meta.query_advice(a3, Rotation::next());
                let w_c = meta.query_advice(a4, Rotation::prev());
                let w_f = meta.query_advice(a4, Rotation::next());

                let w = meta.query_advice(a5, Rotation::cur());

                let decompose_constraint = 
                    w_a +
                    w_b * Expression::Constant(F::from(1 << 3)) +
                    w_c * Expression::Constant(F::from(1 << 7)) +
                    w_d * Expression::Constant(F::from(1 << 10)) +
                    w_e * Expression::Constant(F::from(1 << 17)) +
                    w_f * Expression::Constant(F::from(1 << 18)) + 
                    w_g * Expression::Constant(F::from(1 << 19)) -
                    w;

                vec![
                    s_two * decompose_constraint
                ]
            }
        );
        Self {
            a0, a1, a2, a3, a4, a5,
            s_two,
            _marker: PhantomData
        }

    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        w_lo: u16,
        w_hi: u16,
        offset: usize,
    ) -> Result<(Vec<AssignedCell<F,F>>, u32, u32, u32, u32, u32), Error> {
        
        let w = w_lo as u32 + (w_hi as u32) * (1 << 16);
        let w_a = w & 0b111;
        let w_b = (w >> 3) & 0b1111;
        let w_c = (w >> 7) & 0b111;
        let w_d = (w >> 10) & 0b1111111;
        let w_e = (w >> 17) & 0b1;
        let w_f = (w >> 18) & 0b1;
        let w_g = w >> 19;

        self.s_two.enable(region, offset)?;

        region.assign_advice(|| "sd2 g tag", self.a0, offset-1, || Value::known(F::from(create_tag(w_g as u16) as u64)))?;
        region.assign_advice(|| "sd2 g", self.a1, offset-1, || Value::known(F::from(w_g as u64)))?;
        let s_g = region.assign_advice(|| "sd2 g spread", self.a2, offset-1, || Value::known(F::from(create_interleave_num(w_g) as u64)))?;

        let a = region.assign_advice(|| "sd2 a", self.a3, offset-1, || Value::known(F::from(w_a as u64)))?;
        let c = region.assign_advice(|| "sd2 c", self.a4, offset-1, || Value::known(F::from(w_c as u64)))?;

        region.assign_advice(|| "sd2 d tag", self.a0, offset, || Value::known(F::from(create_tag(w_d as u16) as u64)))?;
        region.assign_advice(|| "sd2 d", self.a1, offset, || Value::known(F::from(w_d as u64)))?;
        let s_d = region.assign_advice(|| "sd2 d spread", self.a2, offset, || Value::known(F::from(create_interleave_num(w_d) as u64)))?;

        region.assign_advice(|| "sd2 b tag", self.a0, offset+1, || Value::known(F::from(create_tag(w_b as u16) as u64)))?;
        let b = region.assign_advice(|| "sd2 b", self.a1, offset+1, || Value::known(F::from(w_b as u64)))?;
        region.assign_advice(|| "sd2 b spread", self.a2, offset+1, || Value::known(F::from(create_interleave_num(w_b) as u64)))?;

        region.assign_advice(|| "sd2 e", self.a3, offset+1, || Value::known(F::from(w_e as u64)))?;
        region.assign_advice(|| "sd2 f", self.a4, offset+1, || Value::known(F::from(w_f as u64)))?;

        let res = vec![s_g, s_d, b, a, c];
        Ok((res, w_a, w_b, w_c, w_e, w_f))
    }

}

