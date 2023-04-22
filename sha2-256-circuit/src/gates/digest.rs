use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Region, Value, AssignedCell},
    plonk::{Advice, Column, ConstraintSystem, Expression, Selector, Error},
    poly::Rotation,
};

#[derive(Debug, Clone)]
pub struct DigestConfig<F: FieldExt> {
    pub s_digest: Selector,
    a3: Column<Advice>,
    a4: Column<Advice>,
    a5: Column<Advice>,
    a6: Column<Advice>,
    a7: Column<Advice>,
    a8: Column<Advice>,
    a9: Column<Advice>,
    _marker: PhantomData<F>
}

impl<F: FieldExt> DigestConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        a3: Column<Advice>,
        a4: Column<Advice>,
        a5: Column<Advice>,
        a6: Column<Advice>,
        a7: Column<Advice>,
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let s_digest = meta.selector();
        meta.create_gate(
            "Digest Gate", 
            |meta| {
                let s_digest = meta.query_selector(s_digest);
                let a_lo = meta.query_advice(a3, Rotation::cur());
                let a_hi = meta.query_advice(a4, Rotation::cur());
                let h_lo = meta.query_advice(a5, Rotation::cur());
                let h_hi = meta.query_advice(a6, Rotation::cur());
                let h_n_lo = meta.query_advice(a7, Rotation::cur());
                let h_n_hi = meta.query_advice(a8, Rotation::cur());
                let h_n_c = meta.query_advice(a9, Rotation::cur());

                let lhs = 
                    a_lo + a_hi * Expression::Constant(F::from( 1<< 16)) +
                    h_lo + h_hi * Expression::Constant(F::from( 1<< 16));

                let rhs = 
                    h_n_lo + h_n_hi * Expression::Constant(F::from( 1<< 16)) + 
                    h_n_c * Expression::Constant(F::from( 1<< 32));
                
                vec![
                    s_digest * (lhs - rhs)
                ]
            }
        );

        Self {
            s_digest,
            a3, a4, a5, a6, a7, a8, a9,
            _marker: PhantomData
        }

    }

    pub fn assign(
        &self,
        region: &mut Region<F>,
        h_n_lo: u16,
        h_n_hi: u16,
        h_n_c: u64,
        h_lo: AssignedCell<F, F>,
        h_hi: AssignedCell<F, F>,
        a_lo: AssignedCell<F, F>,
        a_hi: AssignedCell<F, F>,
        offset: usize
    ) -> Result<Vec<AssignedCell<F, F>>, Error> {
        self.s_digest.enable(region, offset)?;
        a_lo.copy_advice(|| "s_digest a_lo", region, self.a3, offset)?;
        a_hi.copy_advice(|| "s_digest a_hi", region, self.a4, offset)?;
        h_lo.copy_advice(|| "s_digest h_lo", region, self.a5, offset)?;
        h_hi.copy_advice(|| "s_digest h_hi", region, self.a6, offset)?;
        let h_n_lo_c = region.assign_advice(|| "s_digest h_n_lo", self.a7, offset, || Value::known(F::from(h_n_lo as u64)))?;
        let h_n_hi_c = region.assign_advice(|| "s_digest h_n_hi", self.a8, offset, || Value::known(F::from(h_n_hi as u64)))?;
        region.assign_advice(|| "s_digest h_n_c", self.a9, offset, || Value::known(F::from(h_n_c)))?;

        let res = vec![h_n_lo_c, h_n_hi_c];
        Ok(res)
    }

}