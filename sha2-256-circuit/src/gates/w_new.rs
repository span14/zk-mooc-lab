use std::{marker::PhantomData, vec};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};

use crate::utils::{create_range_2_check, reduce4, sigma0, sigma1};

#[derive(Debug, Clone)]
pub struct WNewConfig<F: FieldExt> {
    s_w_new: Selector,
    a5: Column<Advice>,
    a6: Column<Advice>,
    a7: Column<Advice>,
    a8: Column<Advice>,
    a9: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> WNewConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a5: Column<Advice>,
        a6: Column<Advice>,
        a7: Column<Advice>,
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let s_w_new = meta.selector();
        meta.create_gate(
            "W New", 
            |meta| {

                let s_w_new = meta.query_selector(s_w_new);

                let w_0 = meta.query_advice(a5, Rotation::prev());
                let w_16 = meta.query_advice(a5, Rotation::cur());
                
                let sig_0_lo = meta.query_advice(a6, Rotation::prev());
                let sig_0_hi = meta.query_advice(a6, Rotation::cur());

                let sig_1_lo = meta.query_advice(a7, Rotation::prev());
                let sig_1_hi = meta.query_advice(a7, Rotation::cur());

                let w_9_lo = meta.query_advice(a8, Rotation::prev());
                let w_9_hi = meta.query_advice(a8, Rotation::cur());

                let carry = meta.query_advice(a9, Rotation::cur());

                let reduce_constraint = 
                    w_0 + 
                    w_9_lo + w_9_hi * Expression::Constant(F::from(1 << 16)) +
                    sig_0_lo + sig_0_hi * Expression::Constant(F::from(1 << 16)) +
                    sig_1_lo + sig_1_hi * Expression::Constant(F::from(1 << 16)) -
                    w_16 - carry.clone() * Expression::Constant(F::from(1 << 32));
                
                let carry_constraint = create_range_2_check(carry);

                vec![
                    s_w_new * (reduce_constraint + carry_constraint)
                ]
            } 
        );

        Self {
            s_w_new,
            a5, a6, a7, a8, a9,
            _marker: PhantomData
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        w_i_16_lo: u16,
        w_i_16_hi: u16,
        w_i_15_lo: u16,
        w_i_15_hi: u16,
        w_i_7_lo: u16,
        w_i_7_hi: u16,
        w_i_2_lo: u16,
        w_i_2_hi: u16,
        offset: usize,
    ) -> Result<(Vec<AssignedCell<F, F>>, u32), Error>{
        let (s0_lo, s0_hi) = sigma0(w_i_15_lo, w_i_15_hi);
        let (s1_lo, s1_hi) = sigma1(w_i_2_lo, w_i_2_hi);
        let (new_w, carry) = reduce4(
            s0_lo as u32 + (s0_hi as u32) * (1 << 16), 
            s1_lo as u32 + (s1_hi as u32) * (1 << 16), 
            w_i_16_lo as u32 + (w_i_16_hi as u32) * (1 << 16), 
            w_i_7_lo as u32 + (w_i_7_hi as u32) * (1 << 16)
        );
        self.s_w_new.enable(region, offset)?;
        let w_n = region.assign_advice(|| "New W_(i)", self.a5, offset, || Value::known(F::from(new_w as u64)))?;
        let s0_lo = region.assign_advice(|| "Sigma 0 Lo", self.a6, offset-1, || Value::known(F::from(s0_lo as u64)))?;
        let s0_hi = region.assign_advice(|| "Sigma 0 Hi", self.a6, offset, || Value::known(F::from(s0_hi as u64)))?;
        let s1_lo = region.assign_advice(|| "Sigma 1 Lo", self.a7, offset-1, || Value::known(F::from(s1_lo as u64)))?;
        let s1_hi = region.assign_advice(|| "Sigma 1 Hi", self.a7, offset, || Value::known(F::from(s1_hi as u64)))?;
        region.assign_advice(|| "W_(i-7) Lo", self.a8, offset-1, || Value::known(F::from(w_i_7_lo as u64)))?;
        region.assign_advice(|| "W_(i-7) Hi", self.a8, offset, || Value::known(F::from(w_i_7_hi as u64)))?;
        region.assign_advice(|| "Carry", self.a9, offset, || Value::known(F::from(carry)))?;

        let res = vec![w_n, s0_lo, s0_hi, s1_lo, s1_hi];

        Ok((res, new_w))
    }

}