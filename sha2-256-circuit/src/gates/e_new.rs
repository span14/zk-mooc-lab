use std::{marker::PhantomData, vec};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};

use crate::utils::create_value_2_check;

#[derive(Debug, Clone)]
pub struct ENewConfig<F: FieldExt> {
    s_e_new: Selector,
    a7: Column<Advice>,
    a8: Column<Advice>,
    a9: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> ENewConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a7: Column<Advice>,
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let s_e_new = meta.selector();
        meta.create_gate(
            "E New", 
            |meta| {

                let s_e_new = meta.query_selector(s_e_new);

                let d_lo = meta.query_advice(a7, Rotation::cur());
                let d_hi = meta.query_advice(a7, Rotation::next());

                let e_n_lo = meta.query_advice(a8, Rotation::cur());
                let e_n_hi = meta.query_advice(a8, Rotation::next());
                let e_n_carry = meta.query_advice(a9, Rotation::next());

                let h_p_lo = meta.query_advice(a7, Rotation::prev());
                let h_p_hi = meta.query_advice(a8, Rotation::prev());

                let e_n_constraint = 
                    d_lo + d_hi * Expression::Constant(F::from(1<<16)) +
                    h_p_lo + h_p_hi * Expression::Constant(F::from(1<<16)) -
                    e_n_lo - e_n_hi * Expression::Constant(F::from(1<<16)) -
                    e_n_carry.clone() * Expression::Constant(F::from(1<<32));

                let e_n_carry_constraint = create_value_2_check(e_n_carry);

                vec![
                    s_e_new.clone() * e_n_constraint,
                    s_e_new * e_n_carry_constraint
                ]
            } 
        );

        Self {
            s_e_new,
            a7, a8, a9,
            _marker: PhantomData
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        d_lo: u16,
        d_hi: u16,
        e_lo: u16,
        e_hi: u16,
        e_c: u64,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        self.s_e_new.enable(region, offset)?;
        
        let d_lo_c = region.assign_advice(|| "s_e_new d_lo", self.a7, offset, || Value::known(F::from(d_lo as u64)))?;
        let e_n_lo = region.assign_advice(|| "s_e_new e_n_lo", self.a8, offset, || Value::known(F::from(e_lo as u64)))?;

        let d_hi_c = region.assign_advice(|| "s_e_new d_hi", self.a7, offset+1, || Value::known(F::from(d_hi as u64)))?;
        let e_n_hi = region.assign_advice(|| "s_e_new e_n_hi", self.a8, offset+1, || Value::known(F::from(e_hi as u64)))?;
        region.assign_advice(|| "s_e_new e_n_c", self.a9, offset+1, || Value::known(F::from(e_c)))?;

        let res = vec![e_n_lo, e_n_hi, d_lo_c, d_hi_c];
        Ok(res)

    }

    pub fn assign_steady(
        &self,
        region: &mut Region<F>,
        d_lo: AssignedCell<F, F>,
        d_hi: AssignedCell<F, F>,
        e_lo: u16,
        e_hi: u16,
        e_c: u64,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        self.s_e_new.enable(region, offset)?;
        
        let d_lo_c = d_lo.copy_advice(|| "s_e_new d_lo", region, self.a7, offset)?;
        let e_n_lo = region.assign_advice(|| "s_e_new e_n_lo", self.a8, offset, || Value::known(F::from(e_lo as u64)))?;

        let d_hi_c = d_hi.copy_advice(|| "s_e_new d_hi", region, self.a7, offset+1)?;
        let e_n_hi = region.assign_advice(|| "s_e_new e_n_hi", self.a8, offset+1, || Value::known(F::from(e_hi as u64)))?;
        region.assign_advice(|| "s_e_new e_n_c", self.a9, offset+1, || Value::known(F::from(e_c)))?;

        let res = vec![e_n_lo, e_n_hi, d_lo_c, d_hi_c];
        Ok(res)

    }


}