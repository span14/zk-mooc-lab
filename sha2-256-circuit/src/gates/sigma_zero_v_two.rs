use std::marker::PhantomData;

use crate::utils::{
    create_range_2_check,
    create_spread_2_check,
    create_range_3_check,
    create_spread_3_check,
    create_interleave_num,
    create_tag,
    even_bit,
    odd_bit,
};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};


#[derive(Debug, Clone)]
pub struct Sigma0V2Config<F: FieldExt> {
    a0: Column<Advice>,
    a1: Column<Advice>,
    a2: Column<Advice>,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    a6: Column<Advice>,
    a7: Column<Advice>,
    s_sigma0v2: Selector,
    _marker: PhantomData<F>
}


impl<F: FieldExt> Sigma0V2Config<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
        a6: Column<Advice>,
        a7: Column<Advice>,
    ) -> Self {
        let s_sigma0v2 = meta.selector();

        meta.create_gate(
            "Sigma_0 V2", 
            |meta| {
                let s_sigma0v2 = meta.query_selector(s_sigma0v2);

                let r_e_lo = meta.query_advice(a2, Rotation::prev());
                let r_o_lo = meta.query_advice(a2, Rotation::cur());
                let r_e_hi = meta.query_advice(a2, Rotation::next());
                let r_o_hi = meta.query_advice(a3, Rotation::cur());

                let a = meta.query_advice(a3, Rotation::next());
                let s_a = meta.query_advice(a4, Rotation::next());

                let b_lo = meta.query_advice(a3, Rotation::prev());
                let s_b_lo = meta.query_advice(a4, Rotation::prev());

                let b_hi = meta.query_advice(a5, Rotation::prev());
                let s_b_hi = meta.query_advice(a6, Rotation::prev());

                let b = meta.query_advice(a6, Rotation::cur());

                let c = meta.query_advice(a5, Rotation::next());
                let s_c = meta.query_advice(a6, Rotation::next());

                let s_d = meta.query_advice(a4, Rotation::cur());

                let e = meta.query_advice(a7, Rotation::cur());
                let f = meta.query_advice(a7, Rotation::next());

                let s_g = meta.query_advice(a5, Rotation::cur());

                let lhs = 
                    r_e_lo +
                    r_o_lo * Expression::Constant(F::from(2)) +
                    r_e_hi * Expression::Constant(F::from(1 << 32)) +
                    r_o_hi * Expression::Constant(F::from(1 << 33));

                let rhs = 
                    s_g.clone() * Expression::Constant(F::from(1 << 32)) +
                    f.clone() * Expression::Constant(F::from(1 << 30)) +
                    e.clone() * Expression::Constant(F::from(1 << 28)) + 
                    s_d.clone() * Expression::Constant(F::from(1 << 14)) + 
                    s_c.clone() * Expression::Constant(F::from(1 << 8)) + 
                    s_b_hi.clone() * Expression::Constant(F::from(1 << 4)) + 
                    s_b_lo.clone() +
                    s_b_hi.clone() * Expression::Constant(F::from(1 << 60)) +
                    s_b_lo.clone() * Expression::Constant(F::from(1 << 56)) +
                    s_a.clone() * Expression::Constant(F::from(1 << 50)) +
                    s_g.clone() * Expression::Constant(F::from(1 << 24)) + 
                    f.clone() * Expression::Constant(F::from(1 << 22)) + 
                    e.clone() * Expression::Constant(F::from(1 << 20)) + 
                    s_d.clone() * Expression::Constant(F::from(1 << 6)) + 
                    s_c.clone() +
                    e.clone() * Expression::Constant(F::from(1 << 62)) +
                    s_d.clone() * Expression::Constant(F::from(1 << 48)) +
                    s_c.clone() * Expression::Constant(F::from(1 << 42)) +
                    s_b_hi.clone() * Expression::Constant(F::from(1 << 38)) + 
                    s_b_lo.clone() * Expression::Constant(F::from(1 << 34)) + 
                    s_a.clone() * Expression::Constant(F::from(1 << 28)) + 
                    s_g.clone() * Expression::Constant(F::from(1 << 2)) + 
                    f.clone();
                
                let b_lo_check = create_range_2_check(b_lo.clone());
                let s_b_lo_check = create_spread_2_check(b_lo.clone(), s_b_lo);

                let b_hi_check = create_range_2_check(b_hi.clone());
                let s_b_hi_check = create_spread_2_check(b_hi.clone(), s_b_hi);

                let a_check = create_range_3_check(a.clone());
                let s_a_check = create_spread_3_check(a, s_a);

                let c_check = create_range_3_check(c.clone());
                let s_c_check = create_spread_3_check(c, s_c);

                let b_check = 
                    b_lo + b_hi * Expression::Constant(F::from(1 << 2)) - b;

                vec![
                    s_sigma0v2 * 
                    (   
                        lhs - rhs +
                        b_lo_check +
                        s_b_lo_check + 
                        b_hi_check +
                        s_b_hi_check +
                        a_check +
                        s_a_check +
                        c_check +
                        s_c_check +
                        b_check
                    )
                ]
            } 
        );
        Self {
            a0, a1, a2, a3, a4, a5, a6, a7,
            s_sigma0v2,
            _marker: PhantomData
        }

    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        r_lo: u32,
        r_hi: u32,
        s_w_d: AssignedCell<F, F>,
        s_w_g: AssignedCell<F, F>,
        w_b: AssignedCell<F, F>,
        b: u16,
        w_a: AssignedCell<F, F>,
        a: u16,
        w_c: AssignedCell<F, F>,  
        c: u16,      
        w_e: u16,
        w_f: u16,
        r_e_0_c: AssignedCell<F, F>,
        r_e_1_c: AssignedCell<F, F>,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        let r_e_0 = even_bit(r_lo);
        let r_o_0 = odd_bit(r_lo);
        let r_e_1 = even_bit(r_hi);
        let r_o_1 = odd_bit(r_hi);

        let b_lo = b & 0b11;
        let b_hi = b >> 2;
        let s_b_lo = create_interleave_num(b_lo as u32) as u64;
        let s_b_hi = create_interleave_num(b_hi as u32) as u64;
        let s_a = create_interleave_num(a as u32) as u64;
        self.s_sigma0v2.enable(region, offset)?;

        region.assign_advice(|| "ss0v2 re0 tag", self.a0, offset-1, || Value::known(F::from(create_tag(r_e_0) as u64)))?;
        r_e_0_c.copy_advice(|| "ss0v2 re0", region, self.a1, offset-1)?;
        region.assign_advice(|| "ss0v2 s_re0", self.a2, offset-1, || Value::known(F::from(create_interleave_num(r_e_0 as u32) as u64)))?;

        region.assign_advice(|| "ss0v2 ro0 tag", self.a0, offset, || Value::known(F::from(create_tag(r_o_0) as u64)))?;
        region.assign_advice(|| "ss0v2 ro0", self.a1, offset, || Value::known(F::from(r_o_0 as u64)))?;
        region.assign_advice(|| "ss0v2 s_ro0", self.a2, offset, || Value::known(F::from(create_interleave_num(r_o_0 as u32) as u64)))?;

        region.assign_advice(|| "ss0v2 re1 tag", self.a0, offset+1, || Value::known(F::from(create_tag(r_e_1) as u64)))?;
        r_e_1_c.copy_advice(|| "ss0v2 re1", region, self.a1, offset+1)?;
        region.assign_advice(|| "ss0v2 s_re1", self.a2, offset+1, || Value::known(F::from(create_interleave_num(r_e_1 as u32) as u64)))?;
        
        region.assign_advice(|| "ss0v2 ro1 tag", self.a0, offset+2, || Value::known(F::from(create_tag(r_o_1) as u64)))?;
        region.assign_advice(|| "ss0v2 ro1", self.a1, offset+2, || Value::known(F::from(r_o_1 as u64)))?;
        let s_ro1 = region.assign_advice(|| "ss0v2 s_ro1", self.a2, offset+2, || Value::known(F::from(create_interleave_num(r_o_1 as u32) as u64)))?;
        s_ro1.copy_advice(|| "ss0v2 s_ro1 copy", region, self.a3, offset)?;

        region.assign_advice(|| "ss0v2 b_lo", self.a3, offset-1, || Value::known(F::from(b_lo as u64)))?;
        region.assign_advice(|| "ss0v2 s_b_lo", self.a4, offset-1, || Value::known(F::from(s_b_lo)))?;

        region.assign_advice(|| "ss0v2 b_hi", self.a5, offset-1, || Value::known(F::from(b_hi as u64)))?;
        region.assign_advice(|| "ss0v2 s_b_hi", self.a6, offset-1, || Value::known(F::from(s_b_hi)))?;

        let s_w_d = s_w_d.copy_advice(|| "ss0v2 s_d", region, self.a4, offset)?;
        let s_w_g = s_w_g.copy_advice(|| "ss0v2 s_g", region, self.a5, offset)?;
        let w_b = w_b.copy_advice(|| "ss0v2 b", region, self.a6, offset)?;
        let w_a = w_a.copy_advice(|| "ss0v2 a", region, self.a3, offset+1)?;
        region.assign_advice(|| "ss0v2 s_a", self.a4, offset+1, || Value::known(F::from(s_a)))?;
        let w_c = w_c.copy_advice(|| "ss0v2 c", region, self.a5, offset+1)?;
        region.assign_advice(|| "ss0v2 s_c", self.a6, offset+1, || Value::known(F::from(create_interleave_num(c as u32) as u64)))?;

        region.assign_advice(|| "ss0v2 e", self.a7, offset, || Value::known(F::from(w_e as u64)))?;
        region.assign_advice(|| "ss0v2 f", self.a7, offset+1, || Value::known(F::from(w_f as u64)))?;
        let res = vec![s_w_d, s_w_g, w_b, w_a, w_c];
        Ok(res)
    }

}

