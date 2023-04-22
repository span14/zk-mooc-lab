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
pub struct SumOneConfig<F: FieldExt> {
    s_sum_one: Selector,
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> SumOneConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_sum_one = meta.selector();
        meta.create_gate(
            "Sum One Gate", 
            |meta| {
                let s_sum_one = meta.query_selector(s_sum_one);
                let s_re_0 = meta.query_advice(a2, Rotation::prev());
                let s_ro_0 = meta.query_advice(a2, Rotation::cur());
                let s_re_1 = meta.query_advice(a2, Rotation::next());
                let s_ro_1 = meta.query_advice(a3, Rotation::cur());
                
                let s_b_lo = meta.query_advice(a3, Rotation::prev());
                let s_b_hi = meta.query_advice(a4, Rotation::prev());
                let s_d = meta.query_advice(a4, Rotation::cur());
                let s_c = meta.query_advice(a5, Rotation::cur());
                let s_a_lo = meta.query_advice(a3, Rotation::next());
                let s_a_hi = meta.query_advice(a4, Rotation::next());

                let lhs = s_re_0 + Expression::Constant(F::from(2)) * s_ro_0 + Expression::Constant(F::from(1<<32)) * 
                                        s_re_1 + Expression::Constant(F::from(1<<33)) * s_ro_1;
                let rhs_1 = s_a_hi.clone() * Expression::Constant(F::from(1 << 58)) + s_a_lo.clone() * Expression::Constant(F::from(1 << 52)) +
                                            s_d.clone() * Expression::Constant(F::from(1 << 38)) + s_c.clone() * Expression::Constant(F::from(1 << 10)) + 
                                            s_b_hi.clone() * Expression::Constant(F::from(1 << 4)) + s_b_lo.clone();
                let rhs_2 = s_b_hi.clone() * Expression::Constant(F::from(1 << 58)) + s_b_lo.clone() * Expression::Constant(F::from(1 << 54)) +
                                            s_a_hi.clone() * Expression::Constant(F::from(1 << 48)) + s_a_lo.clone() * Expression::Constant(F::from(1 << 42)) + 
                                            s_d.clone() * Expression::Constant(F::from(1 << 28)) + s_c.clone();
                let rhs_3 = s_c * Expression::Constant(F::from(1 << 36)) + s_b_hi * Expression::Constant(F::from(1 << 30)) +
                                            s_b_lo * Expression::Constant(F::from(1 << 26)) + s_a_hi * Expression::Constant(F::from(1 << 20)) + 
                                            s_a_lo * Expression::Constant(F::from(1 << 14)) + s_d;
                let rhs = rhs_1 + rhs_2 + rhs_3;

                vec![
                    s_sum_one * (lhs - rhs),
                ]
            }
        );

        Self {
            s_sum_one,
            a0, a1, a2, a3, a4, a5,
            _marker: PhantomData
        }
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        r_lo: u32,
        r_hi: u32,
        s_a_lo: AssignedCell<F, F>,
        s_a_hi: AssignedCell<F, F>,
        s_b_lo: AssignedCell<F, F>,
        s_b_hi: AssignedCell<F, F>,
        s_c: AssignedCell<F, F>,
        s_d: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        self.s_sum_one.enable(region, offset)?;
        let r_e_0 = even_bit(r_lo);
        let r_o_0 = odd_bit(r_lo);
        let r_e_1 = even_bit(r_hi);
        let r_o_1 = odd_bit(r_hi);

        region.assign_advice(|| "s_sum_one r_e_0 tag", self.a0, offset-1, || Value::known(F::from(create_tag(r_e_0) as u64)))?;
        let r_e_0_c = region.assign_advice(|| "s_sum_one r_e_0", self.a1, offset-1, || Value::known(F::from(r_e_0 as u64)))?;
        region.assign_advice(|| "s_sum_one s_r_e_0", self.a2, offset-1, || Value::known(F::from(create_interleave_num(r_e_0 as u32) as u64)))?;
        s_b_lo.copy_advice(|| "s_sum_one s_b_lo", region, self.a3, offset-1)?;
        s_b_hi.copy_advice(|| "s_sum_one s_b_hi", region, self.a4, offset-1)?;


        region.assign_advice(|| "s_sum_one r_o_0 tag", self.a0, offset, || Value::known(F::from(create_tag(r_o_0) as u64)))?;
        region.assign_advice(|| "s_sum_one r_o_0", self.a1, offset, || Value::known(F::from(r_o_0 as u64)))?;
        region.assign_advice(|| "s_sum_one s_r_o_0", self.a2, offset, || Value::known(F::from(create_interleave_num(r_o_0 as u32) as u64)))?;
        s_d.copy_advice(|| "s_sum_one s_d", region, self.a4, offset)?;
        s_c.copy_advice(|| "s_sum_one s_c", region, self.a5, offset)?;

        region.assign_advice(|| "s_sum_one r_e_1 tag", self.a0, offset+1, || Value::known(F::from(create_tag(r_e_1) as u64)))?;
        let r_e_1_c = region.assign_advice(|| "s_sum_one r_e_1", self.a1, offset+1, || Value::known(F::from(r_e_1 as u64)))?;
        region.assign_advice(|| "s_sum_one s_r_e_1", self.a2, offset+1, || Value::known(F::from(create_interleave_num(r_e_1 as u32) as u64)))?;
        s_a_lo.copy_advice(|| "s_sum_one s_a_lo", region, self.a3, offset+1)?;
        s_a_hi.copy_advice(|| "s_sum_one s_a_hi", region, self.a4, offset+1)?;

        region.assign_advice(|| "s_sum_one r_o_1 tag", self.a0, offset+2, || Value::known(F::from(create_tag(r_o_1) as u64)))?;
        region.assign_advice(|| "s_sum_one r_o_1", self.a1, offset+2, || Value::known(F::from(r_o_1 as u64)))?;
        let s_o_1 = region.assign_advice(|| "s_sum_one s_r_o_1", self.a2, offset+2, || Value::known(F::from(create_interleave_num(r_o_1 as u32) as u64)))?;
        s_o_1.copy_advice(|| "s_sum_one s_r_o_0 copy", region, self.a3, offset)?;

        let res = vec![r_e_0_c, r_e_1_c];
        Ok(res)


    }


    
}
