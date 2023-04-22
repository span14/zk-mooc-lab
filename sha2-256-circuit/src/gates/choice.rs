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
pub struct ChoiceConfig<F: FieldExt> {
    s_ch: Selector,
    s_ch_neg: Selector,
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> ChoiceConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_ch = meta.selector();
        let s_ch_neg = meta.selector();
        meta.create_gate(
            "P' = E' + F'", 
            |meta| {
                let s_ch = meta.query_selector(s_ch);
                let s_pe_0 = meta.query_advice(a2, Rotation::prev());
                let s_po_0 = meta.query_advice(a2, Rotation::cur());
                let s_pe_1 = meta.query_advice(a2, Rotation::next());
                let s_po_1 = meta.query_advice(a3, Rotation::cur());

                let s_e_lo = meta.query_advice(a3, Rotation::prev());
                let s_e_hi = meta.query_advice(a4, Rotation::prev());
                let s_f_lo = meta.query_advice(a3, Rotation::next());
                let s_f_hi = meta.query_advice(a4, Rotation::next());

                let lhs = s_pe_0 + Expression::Constant(F::from(2)) * s_po_0 + Expression::Constant(F::from(1<<32)) * 
                                        s_pe_1 + Expression::Constant(F::from(1<<33)) * s_po_1;
                let rhs = s_e_lo + s_e_hi * F::from(1<<32) + 
                                        s_f_lo + s_f_hi * F::from(1<<32);
                vec![s_ch * (lhs - rhs)]
            }
        );

        meta.create_gate(
            "Q' = ^E' + G'", 
            |meta| {
                let s_ch_neg = meta.query_selector(s_ch_neg);
                let s_qe_0 = meta.query_advice(a2, Rotation::prev());
                let s_qo_0 = meta.query_advice(a2, Rotation::cur());
                let s_qe_1 = meta.query_advice(a2, Rotation::next());
                let s_qo_1 = meta.query_advice(a3, Rotation::cur());

                let s_ne_lo = meta.query_advice(a3, Rotation::prev());
                let s_ne_hi = meta.query_advice(a4, Rotation::prev());
                let s_e_lo = meta.query_advice(a5, Rotation::prev());
                let s_e_hi = meta.query_advice(a5, Rotation::cur());
                let s_g_lo = meta.query_advice(a3, Rotation::next());
                let s_g_hi = meta.query_advice(a4, Rotation::next());

                let lhs = s_qe_0 + Expression::Constant(F::from(2)) * s_qo_0 + Expression::Constant(F::from(1<<32)) * 
                                        s_qe_1 + Expression::Constant(F::from(1<<33)) * s_qo_1;
                let rhs = s_ne_lo.clone() + s_ne_hi.clone() * Expression::Constant(F::from(1<<32)) + 
                                        s_g_lo + s_g_hi * Expression::Constant(F::from(1<<32));
                
                let evens = (create_interleave_num((1<<16)-1) as u64) + (create_interleave_num((1<<16)-1) as u64) * (1<<32);
                let even_rhs = s_ne_lo + s_ne_hi * Expression::Constant(F::from(1<<32)) +
                                            s_e_lo + s_e_hi * Expression::Constant(F::from(1<<32));
                vec![
                    s_ch_neg.clone() * (lhs - rhs),
                    s_ch_neg * (Expression::Constant(F::from(evens)) - even_rhs)
                ]
            }
        );


        Self {
            s_ch,
            s_ch_neg,
            a0, a1, a2, a3, a4, a5,
            _marker: PhantomData
        }
    }

    
    pub fn assign_p(
        &self,
        region: &mut Region<F>,
        p_lo: u32,
        p_hi: u32,
        s_e_lo: AssignedCell<F, F>,
        s_e_hi: AssignedCell<F, F>,
        s_f_lo: AssignedCell<F, F>,
        s_f_hi: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        self.s_ch.enable(region, offset)?;
        let p_e_0 = even_bit(p_lo);
        let p_o_0 = odd_bit(p_lo);
        let p_e_1 = even_bit(p_hi);
        let p_o_1 = odd_bit(p_hi);

        region.assign_advice(|| "s_ch p_e_0 tag", self.a0, offset-1, || Value::known(F::from(create_tag(p_e_0) as u64)))?;
        region.assign_advice(|| "s_ch p_e_0", self.a1, offset-1, || Value::known(F::from(p_e_0 as u64)))?;
        region.assign_advice(|| "s_ch s_p_e_0", self.a2, offset-1, || Value::known(F::from(create_interleave_num(p_e_0 as u32) as u64)))?;
        let s_e_lo_c = s_e_lo.copy_advice(|| "s_ch s_e_lo", region, self.a3, offset-1)?;
        let s_e_hi_c = s_e_hi.copy_advice(|| "s_ch s_e_hi", region, self.a4, offset-1)?;
        
        region.assign_advice(|| "s_ch p_o_0 tag", self.a0, offset, || Value::known(F::from(create_tag(p_o_0) as u64)))?;
        region.assign_advice(|| "s_ch p_o_0", self.a1, offset, || Value::known(F::from(p_o_0 as u64)))?;
        region.assign_advice(|| "s_ch s_p_o_0", self.a2, offset, || Value::known(F::from(create_interleave_num(p_o_0 as u32) as u64)))?;

        region.assign_advice(|| "s_ch p_e_1 tag", self.a0, offset+1, || Value::known(F::from(create_tag(p_e_1) as u64)))?;
        region.assign_advice(|| "s_ch p_e_1", self.a1, offset+1, || Value::known(F::from(p_e_1 as u64)))?;
        region.assign_advice(|| "s_ch s_p_e_1", self.a2, offset+1, || Value::known(F::from(create_interleave_num(p_e_1 as u32) as u64)))?;
        let s_f_lo_c = s_f_lo.copy_advice(|| "s_ch s_f_lo", region, self.a3, offset+1)?;
        let s_f_hi_c =  s_f_hi.copy_advice(|| "s_ch s_f_hi", region, self.a4, offset+1)?;

        region.assign_advice(|| "s_ch p_o_1 tag", self.a0, offset+2, || Value::known(F::from(create_tag(p_o_1) as u64)))?;
        let p_o_1_c = region.assign_advice(|| "s_ch p_o_1", self.a1, offset+2, || Value::known(F::from(p_o_1 as u64)))?;
        let s_p_o_1 = region.assign_advice(|| "s_ch s_p_o_1", self.a2, offset+2, || Value::known(F::from(create_interleave_num(p_o_1 as u32) as u64)))?;
        s_p_o_1.copy_advice(|| "s_ch s_p_o_1 copy", region, self.a3, offset)?;

        let res = vec![p_o_1_c, s_e_lo_c, s_e_hi_c, s_f_lo_c, s_f_hi_c];
        Ok(res)

    }

    pub fn assign_q(
        &self,
        region: &mut Region<F>,
        q_lo: u32,
        q_hi: u32,
        q_o_lo_c: AssignedCell<F, F>,
        q_o_hi_c: AssignedCell<F, F>,
        s_e_n_lo: u32,
        s_e_n_hi: u32,
        s_e_lo: AssignedCell<F, F>,
        s_e_hi: AssignedCell<F, F>,
        s_g_lo: AssignedCell<F, F>,
        s_g_hi: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        self.s_ch_neg.enable(region, offset)?;
        let q_e_0 = even_bit(q_lo);
        let q_o_0 = odd_bit(q_lo);
        let q_e_1 = even_bit(q_hi);
        let q_o_1 = odd_bit(q_hi);

        region.assign_advice(|| "s_ch_neg q_e_0 tag", self.a0, offset-1, || Value::known(F::from(create_tag(q_e_0) as u64)))?;
        region.assign_advice(|| "s_ch_neg q_e_0", self.a1, offset-1, || Value::known(F::from(q_e_0 as u64)))?;
        region.assign_advice(|| "s_ch_neg s_q_e_0", self.a2, offset-1, || Value::known(F::from(create_interleave_num(q_e_0 as u32) as u64)))?;
        region.assign_advice(|| "s_ch_neg s_e_n_lo", self.a3, offset-1, || Value::known(F::from(s_e_n_lo as u64)))?;
        region.assign_advice(|| "s_ch_neg s_e_n_hi", self.a4, offset-1, || Value::known(F::from(s_e_n_hi as u64)))?;
        let s_e_lo_c = s_e_lo.copy_advice(|| "s_ch_neg s_e_lo", region, self.a5, offset-1)?;

        region.assign_advice(|| "s_ch_neg q_o_0 tag", self.a0, offset, || Value::known(F::from(create_tag(q_o_0) as u64)))?;
        q_o_lo_c.copy_advice(|| "s_ch_neg q_o_0", region, self.a1, offset)?;
        region.assign_advice(|| "s_ch_neg s_q_o_0", self.a2, offset, || Value::known(F::from(create_interleave_num(q_o_0 as u32) as u64)))?;
        let s_e_hi_c = s_e_hi.copy_advice(|| "s_ch_neg s_e_hi", region, self.a5, offset)?;

        region.assign_advice(|| "s_ch_neg q_e_1 tag", self.a0, offset+1, || Value::known(F::from(create_tag(q_e_1) as u64)))?;
        region.assign_advice(|| "s_ch_neg q_e_1", self.a1, offset+1, || Value::known(F::from(q_e_1 as u64)))?;
        region.assign_advice(|| "s_ch_neg s_q_e_1", self.a2, offset+1, || Value::known(F::from(create_interleave_num(q_e_1 as u32) as u64)))?;
        s_g_lo.copy_advice(|| "s_ch_neg s_g_lo", region, self.a3, offset+1)?;
        s_g_hi.copy_advice(|| "s_ch_neg s_g_hi", region, self.a4, offset+1)?;

        region.assign_advice(|| "s_ch_neg q_o_1 tag", self.a0, offset+2, || Value::known(F::from(create_tag(q_o_1) as u64)))?;
        q_o_hi_c.copy_advice(|| "s_ch_neg q_o_1", region, self.a1, offset+2)?;
        let s_q_o_1 = region.assign_advice(|| "s_ch_neg s_q_o_1", self.a2, offset+2, || Value::known(F::from(create_interleave_num(q_o_1 as u32) as u64)))?;
        s_q_o_1.copy_advice(|| "s_ch_neg s_q_o_1 copy", region, self.a3, offset)?;
        let res = vec![s_e_lo_c, s_e_hi_c];

        Ok(res)
    }
    
}
