use std::{marker::PhantomData, vec};

use crate::utils::create_range_2_check;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};


#[derive(Debug, Clone)]
pub struct ANewConfig<F: FieldExt> {
    s_a_new: Selector,
    a1: Column<Advice>,
    a3: Column<Advice>,
    a6: Column<Advice>,
    a7: Column<Advice>,
    a8: Column<Advice>,
    a9: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> ANewConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a1: Column<Advice>,
        a3: Column<Advice>,
        a6: Column<Advice>,
        a7: Column<Advice>,
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let s_a_new = meta.selector();
        meta.create_gate(
            "A New", 
            |meta| {

                let s_a_new = meta.query_selector(s_a_new);

                let maj_lo = meta.query_advice(a1, Rotation::cur());
                let maj_hi = meta.query_advice(a3, Rotation::prev());

                let sum_zero_lo = meta.query_advice(a6, Rotation::cur());
                let sum_zero_hi = meta.query_advice(a6, Rotation::next());

                let h_prime_lo = meta.query_advice(a7, Rotation::prev());
                let h_prime_hi = meta.query_advice(a8, Rotation::prev());

                let a_n_lo = meta.query_advice(a8, Rotation::cur());
                let a_n_hi = meta.query_advice(a8, Rotation::next());
                let a_n_carry = meta.query_advice(a9, Rotation::cur());

                let a_n_constraint = 
                    h_prime_lo + h_prime_hi * Expression::Constant(F::from(1<<16)) +
                    sum_zero_lo + sum_zero_hi * Expression::Constant(F::from(1<<16)) +
                    maj_lo + maj_hi * Expression::Constant(F::from(1<<16)) -
                    a_n_lo - a_n_hi * Expression::Constant(F::from(1<<16)) -
                    a_n_carry.clone() * Expression::Constant(F::from(1<<32));

                let a_n_carry_constraint = create_range_2_check(a_n_carry);

                vec![
                    s_a_new.clone() * a_n_constraint,
                    s_a_new * a_n_carry_constraint
                ]
            } 
        );

        Self {
            s_a_new,
            a1, a3, a6, a7, a8, a9,
            _marker: PhantomData
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        a_lo: u16,
        a_hi: u16,
        a_c: u64,
        h_prime_lo: AssignedCell<F, F>,
        h_prime_hi: AssignedCell<F, F>,
        sum_lo: AssignedCell<F, F>,
        sum_hi: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        
        self.s_a_new.enable(region, offset)?;

        h_prime_lo.copy_advice(|| "s_a_new h_prime_lo", region, self.a7, offset-1)?;
        h_prime_hi.copy_advice(|| "s_a_new h_prime_hi", region, self.a8, offset-1)?;

        sum_lo.copy_advice(|| "s_a_new sum_zero_lo", region, self.a6, offset)?;
        let a_lo = region.assign_advice(|| "s_a_new a_new lo", self.a8, offset, || Value::known(F::from(a_lo as u64)))?;
        region.assign_advice(|| "s_a_new a_new carry", self.a9, offset, || Value::known(F::from(a_c)))?;

        sum_hi.copy_advice(|| "s_a_new sum_zero_hi", region, self.a6, offset+1)?;
        let a_hi = region.assign_advice(|| "s_a_new a_new hi", self.a8, offset+1, || Value::known(F::from(a_hi as u64)))?;

        let res = vec![a_lo, a_hi];
        Ok(res)


    }

}