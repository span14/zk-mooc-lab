use std::marker::PhantomData;

use crate::utils::{
    even_bit,
    odd_bit,    
    create_interleave_num,
    create_tag
};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct MajConfig<F: FieldExt> {
    s_maj: Selector,
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> MajConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_maj = meta.selector();
        meta.create_gate(
            "Maj Gate", 
            |meta| {
                let s_maj = meta.query_selector(s_maj);
                let s_me_0 = meta.query_advice(a2, Rotation::prev());
                let s_mo_0 = meta.query_advice(a2, Rotation::cur());
                let s_me_1 = meta.query_advice(a2, Rotation::next());
                let s_mo_1 = meta.query_advice(a3, Rotation::cur());

                let s_a_lo = meta.query_advice(a4, Rotation::prev());
                let s_a_hi = meta.query_advice(a5, Rotation::prev());
                let s_b_lo = meta.query_advice(a4, Rotation::cur());
                let s_b_hi = meta.query_advice(a5, Rotation::cur());
                let s_c_lo = meta.query_advice(a4, Rotation::next());
                let s_c_hi = meta.query_advice(a5, Rotation::next());

                let lhs = s_me_0 + Expression::Constant(F::from(2)) * s_mo_0 + Expression::Constant(F::from(1<<32)) * 
                                        s_me_1 + Expression::Constant(F::from(1<<33)) * s_mo_1;
                let rhs = s_a_lo + s_a_hi * F::from(1<<32) + 
                                        s_b_lo + s_b_hi * F::from(1<<32) + 
                                        s_c_lo + s_c_hi * F::from(1<<32);
                vec![s_maj * (lhs - rhs)]
            }
        );

        Self {
            s_maj,
            a0, a1, a2, a3, a4, a5,
            _marker: PhantomData
        }
    }
    
    pub fn assign(
        &self,
        region: &mut Region<F>,
        m_lo: u32,
        m_hi: u32,
        s_a_lo: AssignedCell<F, F>,
        s_a_hi: AssignedCell<F, F>,
        s_b_lo: AssignedCell<F, F>,
        s_b_hi: AssignedCell<F, F>,
        s_c_lo: AssignedCell<F, F>,
        s_c_hi: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        self.s_maj.enable(region, offset)?;
        let m_e_0 = even_bit(m_lo);
        let m_o_0 = odd_bit(m_lo);
        let m_e_1 = even_bit(m_hi);
        let m_o_1 = odd_bit(m_hi);

        region.assign_advice(|| "s_maj m_e_0 tag", self.a0, offset-1, || Value::known(F::from(create_tag(m_e_0) as u64)))?;
        region.assign_advice(|| "s_maj m_e_0", self.a1, offset-1, || Value::known(F::from(m_e_0 as u64)))?;
        region.assign_advice(|| "s_maj s_m_e_0", self.a2, offset-1, || Value::known(F::from(create_interleave_num(m_e_0 as u32) as u64)))?;
        let s_a_lo_c = s_a_lo.copy_advice(|| "s_maj s_a_lo", region, self.a4, offset-1)?;
        let s_a_hi_c = s_a_hi.copy_advice(|| "s_maj s_a_hi", region, self.a5, offset-1)?;
        
        region.assign_advice(|| "s_maj m_o_0 tag", self.a0, offset, || Value::known(F::from(create_tag(m_o_0) as u64)))?;
        region.assign_advice(|| "s_maj m_o_0", self.a1, offset, || Value::known(F::from(m_o_0 as u64)))?;
        region.assign_advice(|| "s_maj s_m_o_0", self.a2, offset, || Value::known(F::from(create_interleave_num(m_o_0 as u32) as u64)))?;
        let s_b_lo_c = s_b_lo.copy_advice(|| "s_maj s_b_lo", region, self.a4, offset)?;
        let s_b_hi_c = s_b_hi.copy_advice(|| "s_maj s_b_hi", region, self.a5, offset)?;

        region.assign_advice(|| "s_maj m_e_1 tag", self.a0, offset+1, || Value::known(F::from(create_tag(m_e_1) as u64)))?;
        region.assign_advice(|| "s_maj m_e_1", self.a1, offset+1, || Value::known(F::from(m_e_1 as u64)))?;
        region.assign_advice(|| "s_maj s_m_e_1", self.a2, offset+1, || Value::known(F::from(create_interleave_num(m_e_1 as u32) as u64)))?;
        let s_c_lo_c = s_c_lo.copy_advice(|| "s_maj s_c_lo", region, self.a4, offset+1)?;
        let s_c_hi_c = s_c_hi.copy_advice(|| "s_maj s_c_hi", region, self.a5, offset+1)?;

        region.assign_advice(|| "s_maj m_o_1 tag", self.a0, offset+2, || Value::known(F::from(create_tag(m_o_1) as u64)))?;
        let m_o_1_c = region.assign_advice(|| "s_maj m_o_1", self.a1, offset+2, || Value::known(F::from(m_o_1 as u64)))?;
        let s_m_o_1 = region.assign_advice(|| "s_maj s_m_o_1", self.a2, offset+2, || Value::known(F::from(create_interleave_num(m_o_1 as u32) as u64)))?;
        m_o_1_c.copy_advice(|| "s_maj m_o_1 copy", region, self.a3, offset-1)?;
        s_m_o_1.copy_advice(|| "s_maj s_m_o_1 copy", region, self.a3, offset)?;

        let res = vec![s_a_lo_c, s_a_hi, s_b_lo_c, s_b_hi_c, s_c_lo_c, s_c_hi_c];

        Ok(res)
    }
}
