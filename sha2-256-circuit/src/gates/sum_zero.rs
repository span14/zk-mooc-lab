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
pub struct SumZeroConfig<F: FieldExt> {
    s_sum_zero: Selector,
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> SumZeroConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_sum_zero = meta.selector();
        meta.create_gate(
            "Sum Zero Gate", 
            |meta| {
                let s_sum_zero = meta.query_selector(s_sum_zero);
                let s_re_0 = meta.query_advice(a2, Rotation::prev());
                let s_ro_0 = meta.query_advice(a2, Rotation::cur());
                let s_re_1 = meta.query_advice(a2, Rotation::next());
                let s_ro_1 = meta.query_advice(a3, Rotation::cur());
                
                let s_c_lo = meta.query_advice(a3, Rotation::prev());
                let s_c_mi = meta.query_advice(a4, Rotation::prev());
                let s_c_hi = meta.query_advice(a4, Rotation::next());
                let s_d = meta.query_advice(a4, Rotation::cur());
                let s_b = meta.query_advice(a5, Rotation::cur());
                let s_a = meta.query_advice(a3, Rotation::next());

                let lhs = s_re_0 + Expression::Constant(F::from(2)) * s_ro_0 + Expression::Constant(F::from(1<<32)) * 
                                        s_re_1 + Expression::Constant(F::from(1<<33)) * s_ro_1;
                let rhs_1 = s_a.clone() * Expression::Constant(F::from(1 << 60)) + s_d.clone() * Expression::Constant(F::from(1 << 40)) +
                                            s_c_hi.clone() * Expression::Constant(F::from(1 << 34)) + s_c_mi.clone() * Expression::Constant(F::from(1 << 28)) + 
                                            s_c_lo.clone() * Expression::Constant(F::from(1 << 22)) + s_b.clone();
                let rhs_2 = s_b.clone() * Expression::Constant(F::from(1 << 42)) + s_a.clone() * Expression::Constant(F::from(1 << 38)) +
                                            s_d.clone() * Expression::Constant(F::from(1 << 18)) + s_c_hi.clone() * Expression::Constant(F::from(1 << 12)) + 
                                            s_c_mi.clone() * Expression::Constant(F::from(1 << 6)) + s_c_lo.clone();
                let rhs_3 = s_c_hi * Expression::Constant(F::from(1 << 58)) + s_c_mi * Expression::Constant(F::from(1 << 52)) +
                                            s_c_lo * Expression::Constant(F::from(1 << 46)) + s_b * Expression::Constant(F::from(1 << 24)) + 
                                            s_a * Expression::Constant(F::from(1 << 20)) + s_d;
                let rhs = rhs_1 + rhs_2 + rhs_3;

                vec![
                    s_sum_zero.clone() * (lhs - rhs),
                ]
            }
        );

        Self {
            s_sum_zero,
            a0, a1, a2, a3, a4, a5,
            _marker: PhantomData
        }
    }
    
    pub fn assign(
        &self,
        region: &mut Region<F>,
        r_lo: u32,
        r_hi: u32,
        s_a: AssignedCell<F, F>,
        s_b: AssignedCell<F, F>,
        s_c_lo: AssignedCell<F, F>,
        s_c_mi: AssignedCell<F, F>,
        s_c_hi: AssignedCell<F, F>,
        s_d: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<Vec<AssignedCell<F, F>>, Error>{

        self.s_sum_zero.enable(region, offset)?;
        let r_e_0 = even_bit(r_lo);
        let r_o_0 = odd_bit(r_lo);
        let r_e_1 = even_bit(r_hi);
        let r_o_1 = odd_bit(r_hi);

        region.assign_advice(|| "s_sum_zero r_e_0 tag", self.a0, offset-1, || Value::known(F::from(create_tag(r_e_0) as u64)))?;
        let r_e_0_c = region.assign_advice(|| "s_sum_zero r_e_0", self.a1, offset-1, || Value::known(F::from(r_e_0 as u64)))?;
        region.assign_advice(|| "s_sum_zero s_r_e_0", self.a2, offset-1, || Value::known(F::from(create_interleave_num(r_e_0 as u32) as u64)))?;
        s_c_lo.copy_advice(|| "s_sum_zero s_c_lo", region, self.a3, offset-1)?;
        s_c_mi.copy_advice(|| "s_sum_zero s_c_mi", region, self.a4, offset-1)?;


        region.assign_advice(|| "s_sum_zero r_o_0 tag", self.a0, offset, || Value::known(F::from(create_tag(r_o_0) as u64)))?;
        region.assign_advice(|| "s_sum_zero r_o_0", self.a1, offset, || Value::known(F::from(r_o_0 as u64)))?;
        region.assign_advice(|| "s_sum_zero s_r_o_0", self.a2, offset, || Value::known(F::from(create_interleave_num(r_o_0 as u32) as u64)))?;
        s_d.copy_advice(|| "s_sum_zero s_d", region, self.a4, offset)?;
        s_b.copy_advice(|| "s_sum_zero s_b", region, self.a5, offset)?;

        region.assign_advice(|| "s_sum_zero r_e_1 tag", self.a0, offset+1, || Value::known(F::from(create_tag(r_e_1) as u64)))?;
        let r_e_1_c = region.assign_advice(|| "s_sum_zero r_e_1", self.a1, offset+1, || Value::known(F::from(r_e_1 as u64)))?;
        region.assign_advice(|| "s_sum_zero s_r_e_1", self.a2, offset+1, || Value::known(F::from(create_interleave_num(r_e_1 as u32) as u64)))?;
        s_a.copy_advice(|| "s_sum_zero s_a", region, self.a3, offset+1)?;
        s_c_hi.copy_advice(|| "s_sum_zero s_c_hi", region, self.a4, offset+1)?;

        region.assign_advice(|| "s_sum_zero r_o_1 tag", self.a0, offset+2, || Value::known(F::from(create_tag(r_o_1) as u64)))?;
        region.assign_advice(|| "s_sum_zero r_o_1", self.a1, offset+2, || Value::known(F::from(r_o_1 as u64)))?;
        let s_o_1 = region.assign_advice(|| "s_sum_zero s_r_o_1", self.a2, offset+2, || Value::known(F::from(create_interleave_num(r_o_1 as u32) as u64)))?;
        s_o_1.copy_advice(|| "s_sum_zero s_r_o_0 copy", region, self.a3, offset)?;

        let res = vec![r_e_0_c, r_e_1_c];
        Ok(res)


    }
}
