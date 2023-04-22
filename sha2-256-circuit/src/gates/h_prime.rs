use std::{marker::PhantomData, vec};

use crate::utils::create_value_4_check;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};


#[derive(Debug, Clone)]
pub struct HPrimeConfig<F: FieldExt> {
    s_h_prime: Selector,
    a1: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    a6: Column<Advice>,
    a7: Column<Advice>,
    a8: Column<Advice>,
    a9: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> HPrimeConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a1: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
        a6: Column<Advice>,
        a7: Column<Advice>,
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let s_h_prime = meta.selector();

        meta.create_gate(
            "H Prime", 
            |meta| {

                let s_h_prime = meta.query_selector(s_h_prime);
                let sum_one_lo = meta.query_advice(a4, Rotation::cur());
                let sum_one_hi = meta.query_advice(a5, Rotation::cur());
                
                let q_lo = meta.query_advice(a5, Rotation::prev());
                let q_hi = meta.query_advice(a5, Rotation::next());

                let p_lo = meta.query_advice(a1, Rotation::cur());
                let p_hi = meta.query_advice(a6, Rotation::next());

                let k_lo = meta.query_advice(a6, Rotation::prev());
                let k_hi = meta.query_advice(a6, Rotation::cur());

                let h_lo = meta.query_advice(a7, Rotation::prev());
                let h_hi = meta.query_advice(a7, Rotation::cur());

                let w_lo = meta.query_advice(a8, Rotation::prev());
                let w_hi = meta.query_advice(a8, Rotation::cur());

                let h_p_lo = meta.query_advice(a7, Rotation::next());
                let h_p_hi = meta.query_advice(a8, Rotation::next());
                let h_p_carry = meta.query_advice(a9, Rotation::next());

                let h_prime_constraint = 
                    h_lo + h_hi * Expression::Constant(F::from(1<<16)) +
                    sum_one_lo + sum_one_hi * Expression::Constant(F::from(1<<16)) + 
                    k_lo + k_hi * Expression::Constant(F::from(1<<16)) +
                    w_lo + w_hi * Expression::Constant(F::from(1<<16)) +
                    p_lo + p_hi * Expression::Constant(F::from(1<<16)) + 
                    q_lo + q_hi * Expression::Constant(F::from(1<<16)) -
                    h_p_lo - h_p_hi * Expression::Constant(F::from(1<<16)) - 
                    h_p_carry.clone() * Expression::Constant(F::from(1<<32));

                let h_prime_carry_constraint = create_value_4_check(h_p_carry);

                vec![
                    s_h_prime.clone() * h_prime_constraint,
                    s_h_prime * h_prime_carry_constraint
                ]
            } 
        );

        Self {
            s_h_prime,
            a1, a4, a5, a6, a7, a8, a9,
            _marker: PhantomData
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        h_lo: u16,
        h_hi: u16,
        h_prime_lo: u16,
        h_prime_hi: u16,
        h_prime_c: u64,
        k_lo: u16,
        k_hi: u16,
        p_hi: AssignedCell<F, F>,
        q_lo: u16,
        q_hi: u16,
        sum_lo: AssignedCell<F, F>,
        sum_hi: AssignedCell<F, F>,
        w_lo: AssignedCell<F, F>,
        w_hi: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        self.s_h_prime.enable(region, offset)?;

        let q_lo_c = region.assign_advice(|| "h_prime q_lo", self.a5, offset-1, || Value::known(F::from(q_lo as u64)))?;
        region.assign_advice(|| "h_prime k_lo", self.a6, offset-1, || Value::known(F::from(k_lo as u64)))?;
        let h_lo_c = region.assign_advice(|| "h_prime h_lo", self.a7, offset-1, || Value::known(F::from(h_lo as u64)))?;
        w_lo.copy_advice(|| "h_prime w_lo", region, self.a8, offset-1)?;

        sum_lo.copy_advice(|| "h_prime sum_lo", region, self.a4, offset)?;
        sum_hi.copy_advice(|| "h_prime sum_hi", region, self.a5, offset)?;
        region.assign_advice(|| "h_prime k_hi", self.a6, offset, || Value::known(F::from(k_hi as u64)))?;
        let h_hi_c = region.assign_advice(|| "h_prime h_hi", self.a7, offset, || Value::known(F::from(h_hi as u64)))?;
        w_hi.copy_advice(|| "h_prime w_hi", region, self.a8, offset)?;

        let q_hi_c = region.assign_advice(|| "h_prime q_hi", self.a5, offset+1, || Value::known(F::from(q_hi as u64)))?;
        p_hi.copy_advice(|| "h_prime p_hi", region, self.a6, offset+1)?;
        let h_p_lo_c = region.assign_advice(|| "h_prime h_prime_lo", self.a7, offset+1, || Value::known(F::from(h_prime_lo as u64)))?;
        let h_p_hi_c = region.assign_advice(|| "h_prime h_prime_hi", self.a8, offset+1, || Value::known(F::from(h_prime_hi as u64)))?;
        region.assign_advice(|| "h_prime h_prime_c", self.a9, offset+1, || Value::known(F::from(h_prime_c)))?;

        let res = vec![h_p_lo_c, h_p_hi_c, q_lo_c, q_hi_c, h_lo_c, h_hi_c];
        Ok(res)

    }

    pub fn assign_steady(
        &self,
        region: &mut Region<F>,
        h_lo: AssignedCell<F, F>,
        h_hi: AssignedCell<F, F>,
        h_prime_lo: u16,
        h_prime_hi: u16,
        h_prime_c: u64,
        k_lo: u16,
        k_hi: u16,
        p_hi: AssignedCell<F, F>,
        q_lo: u16,
        q_hi: u16,
        sum_lo: AssignedCell<F, F>,
        sum_hi: AssignedCell<F, F>,
        w_lo: AssignedCell<F, F>,
        w_hi: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        self.s_h_prime.enable(region, offset)?;

        let q_lo_c = region.assign_advice(|| "h_prime q_lo", self.a5, offset-1, || Value::known(F::from(q_lo as u64)))?;
        region.assign_advice(|| "h_prime k_lo", self.a6, offset-1, || Value::known(F::from(k_lo as u64)))?;
        let h_lo_c = h_lo.copy_advice(|| "h_prime h_lo", region, self.a7, offset-1)?;
        w_lo.copy_advice(|| "h_prime w_lo", region, self.a8, offset-1)?;

        sum_lo.copy_advice(|| "h_prime sum_lo", region, self.a4, offset)?;
        sum_hi.copy_advice(|| "h_prime sum_hi", region, self.a5, offset)?;
        region.assign_advice(|| "h_prime k_hi", self.a6, offset, || Value::known(F::from(k_hi as u64)))?;
        let h_hi_c = h_hi.copy_advice(|| "h_prime h_hi", region, self.a7, offset)?;
        w_hi.copy_advice(|| "h_prime w_hi", region, self.a8, offset)?;

        let q_hi_c = region.assign_advice(|| "h_prime q_hi", self.a5, offset+1, || Value::known(F::from(q_hi as u64)))?;
        p_hi.copy_advice(|| "h_prime p_hi", region, self.a6, offset+1)?;
        let h_p_lo_c = region.assign_advice(|| "h_prime h_prime_lo", self.a7, offset+1, || Value::known(F::from(h_prime_lo as u64)))?;
        let h_p_hi_c = region.assign_advice(|| "h_prime h_prime_hi", self.a8, offset+1, || Value::known(F::from(h_prime_hi as u64)))?;
        region.assign_advice(|| "h_prime h_prime_c", self.a9, offset+1, || Value::known(F::from(h_prime_c)))?;

        let res = vec![h_p_lo_c, h_p_hi_c, q_lo_c, q_hi_c, h_lo_c, h_hi_c];
        Ok(res)

    }


}