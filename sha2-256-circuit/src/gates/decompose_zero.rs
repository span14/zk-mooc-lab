use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};

use crate::utils::{create_interleave_num, create_tag};


#[derive(Debug, Clone)]
pub struct DecomposeZeroConfig<F: FieldExt> {
    pub s_zero: Selector,
    pub a0: Column<Advice>,
    pub a1: Column<Advice>,
    pub a2: Column<Advice>,
    pub a3: Column<Advice>,
    pub a4: Column<Advice>,
    pub a5: Column<Advice>,
    _marker: PhantomData<F>
}


impl<F: FieldExt> DecomposeZeroConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a0: Column<Advice>,
        a1: Column<Advice>,
        a2: Column<Advice>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
    ) -> Self {
        let s_zero = meta.selector();

        meta.create_gate(
            "Decompose Zero", 
            |meta| {
                let s_zero = meta.query_selector(s_zero);

                let w_lo = meta.query_advice(a3, Rotation::cur());
                let w_hi = meta.query_advice(a4, Rotation::cur());

                let w = meta.query_advice(a5, Rotation::cur());

                let decompose_constraint = 
                    w_lo +
                    w_hi * Expression::Constant(F::from(1 << 16)) -
                    w;

                vec![
                    s_zero * decompose_constraint
                ]
            } 
        );
        Self {
            a0,
            a1,
            a2,
            a3,
            a4,
            a5,
            s_zero,
            _marker: PhantomData
        }

    }

    pub fn assign_special_0(
        &self,
        region: &mut Region<F>,
        w_lo: u16,
        w_hi: u16,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        self.s_zero.enable(region, offset)?;
        region.assign_advice(
            || "W0 Low Tag", 
            self.a0, offset, 
            || Value::known(F::from(create_tag(w_lo)))
        )?;
        let w0_lo = region.assign_advice(
            || "W0 Low Value", 
            self.a1, offset, 
            || Value::known(F::from(w_lo as u64))
        )?;
        region.assign_advice(
            || "W0 Low Value Spread", 
            self.a2, offset, 
            || Value::known(F::from(create_interleave_num(w_lo as u32) as u64))
        )?;
        let w0_lo_c = w0_lo.copy_advice(|| "Same W0 Low Value", region, self.a3, offset)?;
        region.assign_advice(
            || "W0", 
            self.a5, offset, 
            || Value::known(F::from((w_lo as u32 + (w_hi as u32) * (1 << 16)) as u64))
        )?;
        region.assign_advice(
            || "W0 High Tag", 
            self.a0, offset+1, 
            || Value::known(F::from(create_tag(w_hi)))
        )?;
        let w0_hi = region.assign_advice(
            || "W0 High Value", 
            self.a1, offset+1, 
            || Value::known(F::from(w_hi as u64))
        )?;
        region.assign_advice(
            || "W0 High Value Spread", 
            self.a2, offset+1, 
            || Value::known(F::from(create_interleave_num(w_hi as u32) as u64))
        )?;
        let w0_hi_c = w0_hi.copy_advice(|| "Same W0 High Value", region, self.a4, offset)?;

        Ok(vec![w0_lo_c, w0_hi_c])
    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        w_lo: u16,
        w_hi: u16,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        self.s_zero.enable(region, offset)?;
        let w_lo_c = region.assign_advice(
            || "W low", 
            self.a3, offset, 
            || Value::known(F::from(w_lo as u64))
        )?;
        let w_hi_c = region.assign_advice(
            || "W high", 
            self.a4, offset, 
            || Value::known(F::from(w_hi as u64))
        )?;
        region.assign_advice(
            || "W", 
            self.a5, offset, 
            || Value::known(F::from((w_lo as u32 + (w_hi as u32) * (1 << 16)) as u64))
        )?;
        Ok(vec![w_lo_c, w_hi_c])
    }

    pub fn assign_special_1(
        &self,
        region: &mut Region<F>,
        w_lo: AssignedCell<F, F>,
        w_hi: AssignedCell<F, F>,
        w: u32,
        offset: usize
    ) -> Result<(), Error> {

        self.s_zero.enable(region, offset)?;
        w_lo.copy_advice(|| "w lo", region, self.a3, offset)?;
        w_hi.copy_advice(|| "w hi", region, self.a4, offset)?;
        region.assign_advice(
            || "w", 
            self.a5, offset, 
            || Value::known(F::from(w as u64))
        )?;
        Ok(())
    }

    pub fn assign_special_2(
        &self,
        region: &mut Region<F>,
        w_lo: AssignedCell<F, F>,
        w_hi: AssignedCell<F, F>,
        w: AssignedCell<F, F>,
        offset: usize
    ) -> Result<(), Error> {

        self.s_zero.enable(region, offset)?;
        w_lo.copy_advice(|| "w lo", region, self.a3, offset)?;
        w_hi.copy_advice(|| "w hi", region, self.a4, offset)?;
        w.copy_advice(|| "w", region, self.a5, offset)?;

        Ok(())
    }


    pub fn assign_special_3(
        &self,
        region: &mut Region<F>,
        w_lo: u16,
        w_hi: u16,
        w: AssignedCell<F, F>,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {

        self.s_zero.enable(region, offset)?;
        let w_lo_c = region.assign_advice(
            || "w low", 
            self.a3, offset, 
            || Value::known(F::from(w_lo as u64))
        )?;
        let w_hi_c = region.assign_advice(
            || "w high", 
            self.a4, offset, 
            || Value::known(F::from(w_hi as u64))
        )?;
        w.copy_advice(|| "w", region, self.a5, offset)?;

        Ok(vec![w_lo_c, w_hi_c])
    }

}

