use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Region},
    plonk::{Advice, Column, ConstraintSystem, Error},
};

use crate::{gates::{
    decompose_abc::DecomposeABCConfig,
    decompose_efg::DecomposeEFGConfig,
    digest::DigestConfig,
    a_new::ANewConfig,
    e_new::ENewConfig,
    h_prime::HPrimeConfig,
    maj::MajConfig,
    choice::ChoiceConfig,
    sum_one::SumOneConfig,
    sum_zero::SumZeroConfig,
}, utils::create_interleave_num};
use crate::utils::{
    choice,
    e_and_f,
    maj,
    maj_r,
    ne_and_g,
    ne_and_g_r,
    sum0,
    sum1,
    sum0_r,
    sum1_r,
    reduce5,
    reduce2,
    reduce3,
};

#[derive(Debug, Clone)]
pub struct CompressionChip<F: FieldExt> {
    pub sd_abc: DecomposeABCConfig<F>,
    pub sd_efg: DecomposeEFGConfig<F>,
    s_a: ANewConfig<F>,
    s_d: DigestConfig<F>,
    s_e: ENewConfig<F>,
    s_hp: HPrimeConfig<F>,
    s_maj: MajConfig<F>,
    s_ch: ChoiceConfig<F>,
    s_so: SumOneConfig<F>,
    s_sz: SumZeroConfig<F>,
}

impl<F: FieldExt> CompressionChip<F> {

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
        a8: Column<Advice>,
        a9: Column<Advice>,
    ) -> Self {
        let sd_abc = DecomposeABCConfig::configure(meta, a0, a1, a2, a3, a4, a5, a6, a7, a8);
        let sd_efg = DecomposeEFGConfig::configure(meta, a0, a1, a2, a3, a4, a5, a6, a7, a8);
        let s_a = ANewConfig::configure(meta, a1, a3, a6, a7, a8, a9);
        let s_d = DigestConfig::configure(meta, a3, a4, a5, a6, a7, a8, a9);
        let s_e = ENewConfig::configure(meta, a7, a8, a9);
        let s_hp = HPrimeConfig::configure(meta, a1, a4, a5, a6, a7, a8, a9);
        let s_maj = MajConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let s_ch = ChoiceConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let s_so = SumOneConfig::configure(meta, a0, a1, a2, a3, a4, a5);
        let s_sz = SumZeroConfig::configure(meta, a0, a1, a2, a3, a4, a5);

        Self {
            sd_abc,
            sd_efg,
            s_a,
            s_d,
            s_e,
            s_ch,
            s_hp,
            s_maj,
            s_so,
            s_sz,
        }
    }

    pub fn load(
        &self,
        region: &mut Region<F>,
        w: Vec<AssignedCell<F, F>>,
        w_val: Vec<u16>,
        k: Vec<u16>,
        v: Vec<u16>,
        offset: usize
    ) -> Result<(Vec<u16>, Vec<AssignedCell<F, F>>), Error> {

        let e = self.sd_efg.assign(
            region, v[8], v[9], offset
        )?;
        let (s1_r_lo, s1_r_hi) = sum1_r(v[8], v[9]);
        let sum_one = self.s_so.assign(
            region, s1_r_lo, s1_r_hi, e[0].clone(), e[1].clone(), 
            e[2].clone(), e[3].clone(), 
            e[4].clone(), e[5].clone(), offset+3
        )?;
        let f = self.sd_efg.assign(
            region, v[10], v[11], offset+6
        )?;
        let g = self.sd_efg.assign(
            region, v[12], v[13], offset+8
        )?;
        let (p_lo, p_hi) = e_and_f(
            v[8], v[9], v[10], v[11]
        );
        let (q_lo, q_hi) = ne_and_g(
            v[8], v[9], v[12], v[13]
        );
        let ch = self.s_ch.assign_p(
            region, p_lo, p_hi, 
            e[6].clone(), e[7].clone(), 
            f[6].clone(), f[7].clone(), offset+11
        )?;
        let ch_out = choice(
            v[8], v[9],
            v[10], v[11],
            v[12], v[13],
        );
        let sum1_out = sum1(v[8], v[9]);

        let (h_prime_lo, h_prime_hi, h_prime_c) = reduce5(
            v[14] as u32 +v[15] as u32 * ( 1<<16 ),
            ch_out, sum1_out, 
            k[0] as u32 + k[1] as u32 * ( 1<<16 ),
            w_val[0] as u32 + w_val[1] as u32 * ( 1<<16 )
        );
        
        let h_prime = self.s_hp.assign(
            region, v[14], v[15], h_prime_lo, h_prime_hi, h_prime_c, 
            k[0], k[1], ch[0].clone(), q_lo, q_hi, 
            sum_one[0].clone(), sum_one[1].clone(), 
            w[0].clone(), w[1].clone(), offset+11
        )?;
        let (e_n_lo, e_n_hi, e_c) = reduce2(
            v[6] as u32 + v[7] as u32 * ( 1<<16), 
            h_prime_lo as u32 + h_prime_hi as u32 * ( 1<<16 )
        );
        let e_n = self.s_e.assign(
            region, v[6], v[7], 
            e_n_lo, e_n_hi, e_c, offset+13
        )?;

        let (q_lo_r, q_hi_r) = ne_and_g_r(
            v[8], v[9], v[12], v[13]
        );
        let ch_not = self.s_ch.assign_q(
            region, q_lo_r, q_hi_r, h_prime[2].clone(), h_prime[3].clone(),
            create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(v[8] as u32),
            create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(v[9] as u32), 
            ch[1].clone(), ch[2].clone(), g[6].clone(), g[7].clone(), 
            offset+15
        )?;

        let a = self.sd_abc.assign(
            region, v[0], v[1], offset+18
        )?;
        let (s0_r_lo, s0_r_hi) = sum0_r(
            v[0], v[1]
        );
        let sum_zero = self.s_sz.assign(
            region, s0_r_lo, s0_r_hi, 
            a[0].clone(), a[1].clone(),
            a[2].clone(), a[3].clone(), 
            a[4].clone(), a[5].clone(), offset+21
        )?;
        let b = self.sd_abc.assign(
            region, v[2], v[3], offset+24
        )?;
        let c = self.sd_abc.assign(
            region, v[4], v[5], offset+26
        )?;
        let (m_lo, m_hi) = maj_r(
            v[0], v[1], v[2], v[3], v[4], v[5]
        );
        let copies = self.s_maj.assign(
            region, m_lo, m_hi, 
            a[6].clone(), a[7].clone(), 
            b[6].clone(), b[7].clone(), 
            c[6].clone(), c[7].clone(), offset+29
        )?;
        let maj_out = maj(
            v[0], v[1], v[2], v[3], v[4], v[5]
        );
        let sum0_out = sum0(v[0], v[1]);
        let (a_n_lo, a_n_hi, a_c) = reduce3(
            sum0_out, maj_out,
            h_prime_lo as u32 + h_prime_hi as u32 * ( 1<< 16),
        );
        let a_n = self.s_a.assign(
            region, 
            a_n_lo, a_n_hi, a_c, 
            h_prime[0].clone(), h_prime[1].clone(), 
            sum_zero[0].clone(), sum_zero[1].clone(), offset+29
        )?;

        let hs = vec![
            (v[0], v[1], a[8].clone(), a[9].clone()),
            (v[2], v[3], b[8].clone(), b[9].clone()),
            (v[4], v[5], c[8].clone(), c[9].clone()),
            (v[6], v[7], e_n[2].clone(), e_n[3].clone()),
            (v[8], v[9], e[8].clone(), e[9].clone()),
            (v[10], v[11], f[8].clone(), f[9].clone()),
            (v[12], v[13], g[8].clone(), g[9].clone()),
            (v[14], v[15], h_prime[4].clone(), h_prime[5].clone()),
        ];

        let mut a_new = (
            a_n_lo, a_n_hi,
            a_n[0].clone(), a_n[1].clone(), 
        );
        let mut b_new = (
            v[0], v[1],
            a[8].clone(), a[9].clone(),
            copies[0].clone(), copies[1].clone()
        );
        let mut c_new = (
            v[2], v[3],
            b[8].clone(), b[9].clone(),
            copies[2].clone(), copies[3].clone()
        );
        let mut d_new = (
            v[4], v[5],
            c[8].clone(), c[9].clone(),
            copies[4].clone(), copies[5].clone()
        );
        let mut e_new = (
            e_n_lo, e_n_hi,
            e_n[0].clone(), e_n[1].clone()
        );
        let mut f_new = (
            v[8], v[9],
            e[8].clone(), e[9].clone(),
            ch_not[0].clone(), ch_not[1].clone()
        );
        let mut g_new = (
            v[10], v[11],
            f[8].clone(), f[9].clone(),
            ch[3].clone(), ch[4].clone()
        );
        let mut h_new = (
            v[12], v[13],
            g[8].clone(), g[9].clone()
        );
        
        for i in 0..63 {
            let e = self.sd_efg.assign_steady(
                region, 
                e_new.0, e_new.1, e_new.2.clone(), e_new.3.clone(),
                offset+24 * i + 32
            )?;
            let (s1_r_lo, s1_r_hi) = sum1_r(
                e_new.0, e_new.1
            );
            let sum_one = self.s_so.assign(
                region, s1_r_lo, s1_r_hi, e[0].clone(), e[1].clone(), 
                e[2].clone(), e[3].clone(), 
                e[4].clone(), e[5].clone(), offset+24 * i + 32 + 3
            )?;
            let (p_lo, p_hi) = e_and_f(
                e_new.0, e_new.1, f_new.0, f_new.1
            );
            let (q_lo, q_hi) = ne_and_g(
                e_new.0, e_new.1, g_new.0, g_new.1
            );
            let ch = self.s_ch.assign_p(
                region, p_lo, p_hi, 
                e[6].clone(), e[7].clone(), 
                f_new.4.clone(), f_new.5.clone(), offset+24 * i + 32 + 7
            )?;
            let ch_out = choice(
                e_new.0, e_new.1,
                f_new.0, f_new.1,
                g_new.0, g_new.1,
            );
            let sum1_out = sum1(e_new.0, e_new.1);
            let (h_prime_lo, h_prime_hi, h_prime_c) = reduce5(
                h_new.0 as u32 + h_new.1 as u32 * ( 1<<16 ),
                ch_out, sum1_out, 
                k[2*(i+1)] as u32 + k[2*(i+1)+1] as u32 * ( 1<<16 ),
                w_val[2*(i+1)] as u32 + w_val[2*(i+1)+1] as u32 * ( 1<<16 )
            );
            let h_prime = self.s_hp.assign_steady(
                region, h_new.2.clone(), h_new.3.clone(), h_prime_lo, h_prime_hi, h_prime_c, 
                k[2*(i+1)], k[2*(i+1)+1], ch[0].clone(), q_lo, q_hi, 
                sum_one[0].clone(), sum_one[1].clone(), 
                w[2*(i+1)].clone(), w[2*(i+1)+1].clone(), offset+24 * i + 32 + 7
            )?;
            let (e_n_lo, e_n_hi, e_c) = reduce2(
                d_new.0 as u32 + d_new.1 as u32 * ( 1<<16), 
                h_prime_lo as u32 + h_prime_hi as u32 * ( 1<<16 )
            );
            let e_n = self.s_e.assign_steady(
                region, d_new.2.clone(), d_new.3.clone(), 
                e_n_lo, e_n_hi, e_c, offset+24 * i + 32 + 9
            )?;
            let (q_lo_r, q_hi_r) = ne_and_g_r(
                e_new.0, e_new.1, g_new.0, g_new.1
            );
            let ch_not = self.s_ch.assign_q(
                region, q_lo_r, q_hi_r, h_prime[2].clone(), h_prime[3].clone(),
                create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(e_new.0 as u32),
                create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(e_new.1 as u32), 
                ch[1].clone(), ch[2].clone(), g_new.4.clone(), g_new.5.clone(), 
                offset+24 * i + 32 + 11
            )?;
            let a = self.sd_abc.assign_steady(
                region, a_new.0, a_new.1,
                a_new.2.clone(), a_new.3.clone(), 
                offset+24 * i + 32 + 14
            )?;
            let (s0_r_lo, s0_r_hi) = sum0_r(a_new.0, a_new.1);
            let sum_zero = self.s_sz.assign(
                region, s0_r_lo, s0_r_hi, 
                a[0].clone(), a[1].clone(),
                a[2].clone(), a[3].clone(), 
                a[4].clone(), a[5].clone(), offset+24 * i + 32 + 17
            )?;
            let (m_lo, m_hi) = maj_r(
                a_new.0, a_new.1, b_new.0, b_new.1, c_new.0, c_new.1
            );
            let copies = self.s_maj.assign(region, m_lo, m_hi, 
                a[6].clone(), a[7].clone(), 
                b_new.4.clone(), b_new.5.clone(), 
                c_new.4.clone(), c_new.5.clone(), offset+24 * i + 32 + 21
            )?;
            let maj_out = maj(
                a_new.0, a_new.1, b_new.0, b_new.1, c_new.0, c_new.1
            );
            let sum0_out = sum0(a_new.0, a_new.1);
            let (a_n_lo, a_n_hi, a_c) = reduce3(
                sum0_out, maj_out,
                h_prime_lo as u32 + h_prime_hi as u32 * ( 1<< 16),
            );
            let a_n = self.s_a.assign(
                region, 
                a_n_lo, a_n_hi, a_c, 
                h_prime[0].clone(), h_prime[1].clone(), 
                sum_zero[0].clone(), sum_zero[1].clone(), offset+24 * i + 32 + 21
            )?;
            h_new.0 = g_new.0;
            h_new.1 = g_new.1;
            h_new.2 = g_new.2.clone();
            h_new.3 = g_new.3.clone();

            g_new.0 = f_new.0;
            g_new.1 = f_new.1;
            g_new.2 = f_new.2.clone();
            g_new.3 = f_new.3.clone();
            g_new.4 = ch[3].clone();
            g_new.5 = ch[4].clone();

            f_new.0 = e_new.0;
            f_new.1 = e_new.1;
            f_new.2 = e[8].clone();
            f_new.3 = e[9].clone();
            f_new.4 = ch_not[0].clone();
            f_new.5 = ch_not[1].clone();

            e_new.0 = e_n_lo;
            e_new.1 = e_n_hi;
            e_new.2 = e_n[0].clone();
            e_new.3 = e_n[1].clone();

            d_new.0 = c_new.0;
            d_new.1 = c_new.1;
            d_new.2 = c_new.2.clone();
            d_new.3 = c_new.3.clone();
            d_new.4 = copies[4].clone();
            d_new.5 = copies[5].clone();

            c_new.0 = b_new.0;
            c_new.1 = b_new.1;
            c_new.2 = b_new.2.clone();
            c_new.3 = b_new.3.clone();
            c_new.4 = copies[2].clone();
            c_new.5 = copies[3].clone();

            b_new.0 = a_new.0;
            b_new.1 = a_new.1;
            b_new.2 = a[8].clone();
            b_new.3 = a[9].clone();
            b_new.4 = copies[0].clone();
            b_new.5 = copies[1].clone();

            a_new.0 = a_n_lo;
            a_new.1 = a_n_hi;
            a_new.2 = a_n[0].clone();
            a_new.3 = a_n[1].clone();
        }
        // H1
        let (h1_lo, h1_hi, h1_c) = reduce2(
            hs[0].0 as u32 + hs[0].1 as u32 * ( 1<<16 ),
            a_new.0 as u32 + a_new.1 as u32 * ( 1<<16 )
        );
        let h1_n = self.s_d.assign(
            region, h1_lo, h1_hi, h1_c, 
            hs[0].2.clone(), hs[0].3.clone(), 
            a_new.2.clone(), a_new.3.clone(), offset+1544
        )?;
        // H2
        let (h2_lo, h2_hi, h2_c) = reduce2(
            hs[1].0 as u32 + hs[1].1 as u32 * ( 1<<16 ),
            b_new.0 as u32 + b_new.1 as u32 * ( 1<<16 )
        );
        let h2_n = self.s_d.assign(
            region, h2_lo, h2_hi, h2_c, 
            hs[1].2.clone(), hs[1].3.clone(), 
            b_new.2.clone(), b_new.3.clone(), offset+1545
        )?;
        // H3
        let (h3_lo, h3_hi, h3_c) = reduce2(
            hs[2].0 as u32 + hs[2].1 as u32 * ( 1<<16 ),
            c_new.0 as u32 + c_new.1 as u32 * ( 1<<16 )
        );
        let h3_n = self.s_d.assign(
            region, h3_lo, h3_hi, h3_c, 
            hs[2].2.clone(), hs[2].3.clone(), 
            c_new.2.clone(), c_new.3.clone(), offset+1546
        )?;
        // H4
        let (h4_lo, h4_hi, h4_c) = reduce2(
            hs[3].0 as u32 + hs[3].1 as u32 * ( 1<<16 ),
            d_new.0 as u32 + d_new.1 as u32 * ( 1<<16 )
        );
        let h4_n = self.s_d.assign(
            region, h4_lo, h4_hi, h4_c, 
            hs[3].2.clone(), hs[3].3.clone(), 
            d_new.2.clone(), d_new.3.clone(), offset+1547
        )?;
        // H5
        let (h5_lo, h5_hi, h5_c) = reduce2(
            hs[4].0 as u32 + hs[4].1 as u32 * ( 1<<16 ),
            e_new.0 as u32 + e_new.1 as u32 * ( 1<<16 )
        );
        let h5_n = self.s_d.assign(
            region, h5_lo, h5_hi, h5_c, 
            hs[4].2.clone(), hs[4].3.clone(), 
            e_new.2.clone(), e_new.3.clone(), offset+1548
        )?;
        // H6
        let (h6_lo, h6_hi, h6_c) = reduce2(
            hs[5].0 as u32 + hs[5].1 as u32 * ( 1<<16 ),
            f_new.0 as u32 + f_new.1 as u32 * ( 1<<16 )
        );
        let h6_n = self.s_d.assign(
            region, h6_lo, h6_hi, h6_c, 
            hs[5].2.clone(), hs[5].3.clone(), 
            f_new.2.clone(), f_new.3.clone(), offset+1549
        )?;
        // H7
        let (h7_lo, h7_hi, h7_c) = reduce2(
            hs[6].0 as u32 + hs[6].1 as u32 * ( 1<<16 ),
            g_new.0 as u32 + g_new.1 as u32 * ( 1<<16 )
        );
        let h7_n = self.s_d.assign(
            region, h7_lo, h7_hi, h7_c, 
            hs[6].2.clone(), hs[6].3.clone(), 
            g_new.2.clone(), g_new.3.clone(), offset+1550
        )?;
        // H8
        let (h8_lo, h8_hi, h8_c) = reduce2(
            hs[7].0 as u32 + hs[7].1 as u32 * ( 1<<16 ),
            h_new.0 as u32 + h_new.1 as u32 * ( 1<<16 )
        );
        let h8_n = self.s_d.assign(
            region, h8_lo, h8_hi, h8_c, 
            hs[7].2.clone(), hs[7].3.clone(), 
            h_new.2.clone(), h_new.3.clone(), offset+1551
        )?;
        let res = (
            vec![
                h1_lo, h1_hi,
                h2_lo, h2_hi,
                h3_lo, h3_hi,
                h4_lo, h4_hi,
                h5_lo, h5_hi,
                h6_lo, h6_hi,
                h7_lo, h7_hi,
                h8_lo, h8_hi
            ],
            vec![
                h1_n[0].clone(), h1_n[1].clone(),
                h2_n[0].clone(), h2_n[1].clone(),
                h3_n[0].clone(), h3_n[1].clone(),
                h4_n[0].clone(), h4_n[1].clone(),
                h5_n[0].clone(), h5_n[1].clone(),
                h6_n[0].clone(), h6_n[1].clone(),
                h7_n[0].clone(), h7_n[1].clone(),
                h8_n[0].clone(), h8_n[1].clone()
            ]
        );
        Ok(res)

    }


    pub fn load_steady(
        &self,
        region: &mut Region<F>,
        w: Vec<AssignedCell<F, F>>,
        w_val: Vec<u16>,
        k: Vec<u16>,
        h: Vec<AssignedCell<F, F>>,
        h_val: Vec<u16>,
        offset: usize,
    ) -> Result<(Vec<u16>, Vec<AssignedCell<F, F>>), Error> {
        
        let e = self.sd_efg.assign_steady(
            region, h_val[8], h_val[9], 
            h[8].clone(), h[9].clone(), offset
        )?;
        let (s1_r_lo, s1_r_hi) = sum1_r(h_val[8], h_val[9]);
        let sum_one = self.s_so.assign(
            region, s1_r_lo, s1_r_hi, e[0].clone(), e[1].clone(), 
            e[2].clone(), e[3].clone(), 
            e[4].clone(), e[5].clone(), offset+3
        )?;
        let f = self.sd_efg.assign_steady(
            region, h_val[10], h_val[11], 
            h[10].clone(), h[11].clone(), offset+6
        )?;
        let g = self.sd_efg.assign_steady(
            region, h_val[12], h_val[13], 
            h[12].clone(), h[13].clone(), offset+8
        )?;
        let (p_lo, p_hi) = e_and_f(
            h_val[8], h_val[9], h_val[10], h_val[11]
        );
        let (q_lo, q_hi) = ne_and_g(
            h_val[8], h_val[9], h_val[12], h_val[13]
        );
        let ch = self.s_ch.assign_p(
            region, p_lo, p_hi, 
            e[6].clone(), e[7].clone(), 
            f[6].clone(), f[7].clone(), offset+11
        )?;
        let ch_out = choice(
            h_val[8], h_val[9],
            h_val[10], h_val[11],
            h_val[12], h_val[13],
        );
        let sum1_out = sum1(h_val[8], h_val[9]);

        let (h_prime_lo, h_prime_hi, h_prime_c) = reduce5(
            h_val[14] as u32 +h_val[15] as u32 * ( 1<<16 ),
            ch_out, sum1_out, 
            k[0] as u32 + k[1] as u32 * ( 1<<16 ),
            w_val[0] as u32 + w_val[1] as u32 * ( 1<<16 )
        );
        let h_prime = self.s_hp.assign_steady(
            region, h[14].clone(), h[15].clone(), h_prime_lo, h_prime_hi, h_prime_c, 
            k[0], k[1], ch[0].clone(), q_lo, q_hi, 
            sum_one[0].clone(), sum_one[1].clone(), 
            w[0].clone(), w[1].clone(), offset+11
        )?;
        let (e_n_lo, e_n_hi, e_c) = reduce2(
            h_val[6] as u32 + h_val[7] as u32 * ( 1<<16), 
            h_prime_lo as u32 + h_prime_hi as u32 * ( 1<<16 )
        );
        let e_n = self.s_e.assign_steady(
            region, h[6].clone(), h[7].clone(), 
            e_n_lo, e_n_hi, e_c, offset+13
        )?;

        let (q_lo_r, q_hi_r) = ne_and_g_r(
            h_val[8], h_val[9], h_val[12], h_val[13]
        );
        let ch_not = self.s_ch.assign_q(
            region, q_lo_r, q_hi_r, h_prime[2].clone(), h_prime[3].clone(),
            create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(h_val[8] as u32),
            create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(h_val[9] as u32), 
            ch[1].clone(), ch[2].clone(), g[6].clone(), g[7].clone(), 
            offset+15
        )?;
        let a = self.sd_abc.assign_steady(
            region, h_val[0], h_val[1],
            h[0].clone(), h[1].clone(), offset+18
        )?;
        let (s0_r_lo, s0_r_hi) = sum0_r(
            h_val[0], h_val[1]
        );
        let sum_zero = self.s_sz.assign(
            region, s0_r_lo, s0_r_hi, 
            a[0].clone(), a[1].clone(),
            a[2].clone(), a[3].clone(), 
            a[4].clone(), a[5].clone(), offset+21
        )?;
        let b = self.sd_abc.assign_steady(
            region, h_val[2], h_val[3], 
            h[2].clone(), h[3].clone(),
            offset+24
        )?;
        let c = self.sd_abc.assign_steady(
            region, h_val[4], h_val[5], 
            h[4].clone(), h[5].clone(),
            offset+26
        )?;
        let (m_lo, m_hi) = maj_r(
            h_val[0], h_val[1], h_val[2], h_val[3], h_val[4], h_val[5]
        );
        let copies = self.s_maj.assign(
            region, m_lo, m_hi, 
            a[6].clone(), a[7].clone(), 
            b[6].clone(), b[7].clone(), 
            c[6].clone(), c[7].clone(), offset+29
        )?;
        let maj_out = maj(
            h_val[0], h_val[1], h_val[2], h_val[3], h_val[4], h_val[5]
        );
        let sum0_out = sum0(h_val[0], h_val[1]);
        let (a_n_lo, a_n_hi, a_c) = reduce3(
            sum0_out, maj_out,
            h_prime_lo as u32 + h_prime_hi as u32 * ( 1<< 16),
        );
        let a_n = self.s_a.assign(
            region, 
            a_n_lo, a_n_hi, a_c, 
            h_prime[0].clone(), h_prime[1].clone(), 
            sum_zero[0].clone(), sum_zero[1].clone(), offset+29
        )?;

        let hs = vec![
            (h_val[0], h_val[1], a[8].clone(), a[9].clone()),
            (h_val[2], h_val[3], b[8].clone(), b[9].clone()),
            (h_val[4], h_val[5], c[8].clone(), c[9].clone()),
            (h_val[6], h_val[7], e_n[2].clone(), e_n[3].clone()),
            (h_val[8], h_val[9], e[8].clone(), e[9].clone()),
            (h_val[10], h_val[11], f[8].clone(), f[9].clone()),
            (h_val[12], h_val[13], g[8].clone(), g[9].clone()),
            (h_val[14], h_val[15], h_prime[4].clone(), h_prime[5].clone()),
        ];

        let mut a_new = (
            a_n_lo, a_n_hi,
            a_n[0].clone(), a_n[1].clone(), 
        );
        let mut b_new = (
            h_val[0], h_val[1],
            a[8].clone(), a[9].clone(),
            copies[0].clone(), copies[1].clone()
        );
        let mut c_new = (
            h_val[2], h_val[3],
            b[8].clone(), b[9].clone(),
            copies[2].clone(), copies[3].clone()
        );
        let mut d_new = (
            h_val[4], h_val[5],
            c[8].clone(), c[9].clone(),
            copies[4].clone(), copies[5].clone()
        );
        let mut e_new = (
            e_n_lo, e_n_hi,
            e_n[0].clone(), e_n[1].clone()
        );
        let mut f_new = (
            h_val[8], h_val[9],
            e[8].clone(), e[9].clone(),
            ch_not[0].clone(), ch_not[1].clone()
        );
        let mut g_new = (
            h_val[10], h_val[11],
            f[8].clone(), f[9].clone(),
            ch[3].clone(), ch[4].clone()
        );
        let mut h_new = (
            h_val[12], h_val[13],
            g[8].clone(), g[9].clone()
        );
        for i in 0..63 {
            let e = self.sd_efg.assign_steady(
                region, 
                e_new.0, e_new.1, e_new.2.clone(), e_new.3.clone(),
                offset+24 * i + 32
            )?;
            let (s1_r_lo, s1_r_hi) = sum1_r(
                e_new.0, e_new.1
            );
            let sum_one = self.s_so.assign(
                region, s1_r_lo, s1_r_hi, e[0].clone(), e[1].clone(), 
                e[2].clone(), e[3].clone(), 
                e[4].clone(), e[5].clone(), offset+24 * i + 32 + 3
            )?;
            let (p_lo, p_hi) = e_and_f(
                e_new.0, e_new.1, f_new.0, f_new.1
            );
            let (q_lo, q_hi) = ne_and_g(
                e_new.0, e_new.1, g_new.0, g_new.1
            );
            let ch = self.s_ch.assign_p(
                region, p_lo, p_hi, 
                e[6].clone(), e[7].clone(), 
                f_new.4.clone(), f_new.5.clone(), offset+24 * i + 32 + 7
            )?;
            let ch_out = choice(
                e_new.0, e_new.1,
                f_new.0, f_new.1,
                g_new.0, g_new.1,
            );
            let sum1_out = sum1(e_new.0, e_new.1);
            let (h_prime_lo, h_prime_hi, h_prime_c) = reduce5(
                h_new.0 as u32 + h_new.1 as u32 * ( 1<<16 ),
                ch_out, sum1_out, 
                k[2*(i+1)] as u32 + k[2*(i+1)+1] as u32 * ( 1<<16 ),
                w_val[2*(i+1)] as u32 + w_val[2*(i+1)+1] as u32 * ( 1<<16 )
            );
            let h_prime = self.s_hp.assign_steady(
                region, h_new.2.clone(), h_new.3.clone(), h_prime_lo, h_prime_hi, h_prime_c, 
                k[2*(i+1)], k[2*(i+1)+1], ch[0].clone(), q_lo, q_hi, 
                sum_one[0].clone(), sum_one[1].clone(), 
                w[2*(i+1)].clone(), w[2*(i+1)+1].clone(), offset+24 * i + 32 + 7
            )?;
            let (e_n_lo, e_n_hi, e_c) = reduce2(
                d_new.0 as u32 + d_new.1 as u32 * ( 1<<16), 
                h_prime_lo as u32 + h_prime_hi as u32 * ( 1<<16 )
            );
            let e_n = self.s_e.assign_steady(
                region, d_new.2.clone(), d_new.3.clone(), 
                e_n_lo, e_n_hi, e_c, offset+24 * i + 32 + 9
            )?;
            let (q_lo_r, q_hi_r) = ne_and_g_r(
                e_new.0, e_new.1, g_new.0, g_new.1
            );
            let ch_not = self.s_ch.assign_q(
                region, q_lo_r, q_hi_r, h_prime[2].clone(), h_prime[3].clone(),
                create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(e_new.0 as u32),
                create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(e_new.1 as u32), 
                ch[1].clone(), ch[2].clone(), g_new.4.clone(), g_new.5.clone(), 
                offset+24 * i + 32 + 11
            )?;
            let a = self.sd_abc.assign_steady(
                region, a_new.0, a_new.1,
                a_new.2.clone(), a_new.3.clone(), 
                offset+24 * i + 32 + 14
            )?;
            let (s0_r_lo, s0_r_hi) = sum0_r(a_new.0, a_new.1);
            let sum_zero = self.s_sz.assign(
                region, s0_r_lo, s0_r_hi, 
                a[0].clone(), a[1].clone(),
                a[2].clone(), a[3].clone(), 
                a[4].clone(), a[5].clone(), offset+24 * i + 32 + 17
            )?;
            let (m_lo, m_hi) = maj_r(
                a_new.0, a_new.1, b_new.0, b_new.1, c_new.0, c_new.1
            );
            let copies = self.s_maj.assign(
                region, m_lo, m_hi, 
                a[6].clone(), a[7].clone(), 
                b_new.4.clone(), b_new.5.clone(), 
                c_new.4.clone(), c_new.5.clone(), offset+24 * i + 32 + 21
            )?;
            let maj_out = maj(
                a_new.0, a_new.1, b_new.0, b_new.1, c_new.0, c_new.1
            );
            let sum0_out = sum0(a_new.0, a_new.1);
            let (a_n_lo, a_n_hi, a_c) = reduce3(
                sum0_out, maj_out,
                h_prime_lo as u32 + h_prime_hi as u32 * ( 1<< 16),
            );
            let a_n = self.s_a.assign(
                region, 
                a_n_lo, a_n_hi, a_c, 
                h_prime[0].clone(), h_prime[1].clone(), 
                sum_zero[0].clone(), sum_zero[1].clone(), offset+24 * i + 32 + 21
            )?;
            h_new.0 = g_new.0;
            h_new.1 = g_new.1;
            h_new.2 = g_new.2.clone();
            h_new.3 = g_new.3.clone();

            g_new.0 = f_new.0;
            g_new.1 = f_new.1;
            g_new.2 = f_new.2.clone();
            g_new.3 = f_new.3.clone();
            g_new.4 = ch[3].clone();
            g_new.5 = ch[4].clone();

            f_new.0 = e_new.0;
            f_new.1 = e_new.1;
            f_new.2 = e[8].clone();
            f_new.3 = e[9].clone();
            f_new.4 = ch_not[0].clone();
            f_new.5 = ch_not[1].clone();

            e_new.0 = e_n_lo;
            e_new.1 = e_n_hi;
            e_new.2 = e_n[0].clone();
            e_new.3 = e_n[1].clone();

            d_new.0 = c_new.0;
            d_new.1 = c_new.1;
            d_new.2 = c_new.2.clone();
            d_new.3 = c_new.3.clone();
            d_new.4 = copies[4].clone();
            d_new.5 = copies[5].clone();

            c_new.0 = b_new.0;
            c_new.1 = b_new.1;
            c_new.2 = b_new.2.clone();
            c_new.3 = b_new.3.clone();
            c_new.4 = copies[2].clone();
            c_new.5 = copies[3].clone();

            b_new.0 = a_new.0;
            b_new.1 = a_new.1;
            b_new.2 = a[8].clone();
            b_new.3 = a[9].clone();
            b_new.4 = copies[0].clone();
            b_new.5 = copies[1].clone();

            a_new.0 = a_n_lo;
            a_new.1 = a_n_hi;
            a_new.2 = a_n[0].clone();
            a_new.3 = a_n[1].clone();
        }
        // H1
        let (h1_lo, h1_hi, h1_c) = reduce2(
            hs[0].0 as u32 + hs[0].1 as u32 * ( 1<<16 ),
            a_new.0 as u32 + a_new.1 as u32 * ( 1<<16 )
        );
        let h1_n = self.s_d.assign(
            region, h1_lo, h1_hi, h1_c, 
            hs[0].2.clone(), hs[0].3.clone(), 
            a_new.2.clone(), a_new.3.clone(), offset+1544
        )?;
        // H2
        let (h2_lo, h2_hi, h2_c) = reduce2(
            hs[1].0 as u32 + hs[1].1 as u32 * ( 1<<16 ),
            b_new.0 as u32 + b_new.1 as u32 * ( 1<<16 )
        );
        let h2_n = self.s_d.assign(
            region, h2_lo, h2_hi, h2_c, 
            hs[1].2.clone(), hs[1].3.clone(), 
            b_new.2.clone(), b_new.3.clone(), offset+1545
        )?;
        // H3
        let (h3_lo, h3_hi, h3_c) = reduce2(
            hs[2].0 as u32 + hs[2].1 as u32 * ( 1<<16 ),
            c_new.0 as u32 + c_new.1 as u32 * ( 1<<16 )
        );
        let h3_n = self.s_d.assign(
            region, h3_lo, h3_hi, h3_c, 
            hs[2].2.clone(), hs[2].3.clone(), 
            c_new.2.clone(), c_new.3.clone(), offset+1546
        )?;
        // H4
        let (h4_lo, h4_hi, h4_c) = reduce2(
            hs[3].0 as u32 + hs[3].1 as u32 * ( 1<<16 ),
            d_new.0 as u32 + d_new.1 as u32 * ( 1<<16 )
        );
        let h4_n = self.s_d.assign(
            region, h4_lo, h4_hi, h4_c, 
            hs[3].2.clone(), hs[3].3.clone(), 
            d_new.2.clone(), d_new.3.clone(), offset+1547
        )?;
        // H5
        let (h5_lo, h5_hi, h5_c) = reduce2(
            hs[4].0 as u32 + hs[4].1 as u32 * ( 1<<16 ),
            e_new.0 as u32 + e_new.1 as u32 * ( 1<<16 )
        );
        let h5_n = self.s_d.assign(
            region, h5_lo, h5_hi, h5_c, 
            hs[4].2.clone(), hs[4].3.clone(), 
            e_new.2.clone(), e_new.3.clone(), offset+1548
        )?;
        // H6
        let (h6_lo, h6_hi, h6_c) = reduce2(
            hs[5].0 as u32 + hs[5].1 as u32 * ( 1<<16 ),
            f_new.0 as u32 + f_new.1 as u32 * ( 1<<16 )
        );
        let h6_n = self.s_d.assign(
            region, h6_lo, h6_hi, h6_c, 
            hs[5].2.clone(), hs[5].3.clone(), 
            f_new.2.clone(), f_new.3.clone(), offset+1549
        )?;
        // H7
        let (h7_lo, h7_hi, h7_c) = reduce2(
            hs[6].0 as u32 + hs[6].1 as u32 * ( 1<<16 ),
            g_new.0 as u32 + g_new.1 as u32 * ( 1<<16 )
        );
        let h7_n = self.s_d.assign(
            region, h7_lo, h7_hi, h7_c, 
            hs[6].2.clone(), hs[6].3.clone(), 
            g_new.2.clone(), g_new.3.clone(), offset+1550
        )?;
        // H8
        let (h8_lo, h8_hi, h8_c) = reduce2(
            hs[7].0 as u32 + hs[7].1 as u32 * ( 1<<16 ),
            h_new.0 as u32 + h_new.1 as u32 * ( 1<<16 )
        );
        let h8_n = self.s_d.assign(
            region, h8_lo, h8_hi, h8_c, 
            hs[7].2.clone(), hs[7].3.clone(), 
            h_new.2.clone(), h_new.3.clone(), offset+1551
        )?;
        let res = (
            vec![
                h1_lo, h1_hi,
                h2_lo, h2_hi,
                h3_lo, h3_hi,
                h4_lo, h4_hi,
                h5_lo, h5_hi,
                h6_lo, h6_hi,
                h7_lo, h7_hi,
                h8_lo, h8_hi
            ],
            vec![
                h1_n[0].clone(), h1_n[1].clone(),
                h2_n[0].clone(), h2_n[1].clone(),
                h3_n[0].clone(), h3_n[1].clone(),
                h4_n[0].clone(), h4_n[1].clone(),
                h5_n[0].clone(), h5_n[1].clone(),
                h6_n[0].clone(), h6_n[1].clone(),
                h7_n[0].clone(), h7_n[1].clone(),
                h8_n[0].clone(), h8_n[1].clone()
            ]
        );
        Ok(res)
    }

}


#[cfg(test)]
mod tests {

    use super::*;
    use std::marker::PhantomData;
    use crate::spread_table::SpreadTableConfig;
    use crate::regions::message_schedule::MessageScheduleChip;
    use halo2_proofs::circuit::{SimpleFloorPlanner, Layouter};
    use halo2_proofs::plonk::{Column, Advice, Circuit};
    use halo2_proofs::poly::Rotation;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr as F};


    #[derive(Debug, Clone)]
    struct SimpleConfig<F: FieldExt, const NUM_BITS: usize> {
        compression_chip: CompressionChip<F>,
        message_schedule_chip: MessageScheduleChip<F>,
        table_config: SpreadTableConfig<F, NUM_BITS>,
    }
    
    impl<F: FieldExt, const NUM_BITS: usize> SimpleConfig<F, NUM_BITS> {
        fn configure(
            meta: &mut ConstraintSystem<F>
        ) -> Self {
            let mut cols: Vec<Column<Advice>> = vec![];
            for i in 0..10 {
                cols.push(meta.advice_column());
                meta.enable_equality(cols[i]);
            }
            let table_config = SpreadTableConfig::configure(meta);
            let compression_chip = CompressionChip::configure(
                meta, 
                cols[0], cols[1], cols[2], cols[3], cols[4], 
                cols[5], cols[6], cols[7], cols[8], cols[9]
            );
            let message_schedule_chip = MessageScheduleChip::configure(
                meta, cols[0], cols[1], cols[2], cols[3], cols[4], 
                cols[5], cols[6], cols[7], cols[8], cols[9]
            );

            meta.lookup("Spread Table 1", |meta| {
                let it = meta.query_advice(cols[0], Rotation::cur());
                let ita = meta.query_advice(cols[1], Rotation::cur());
                let is = meta.query_advice(cols[2], Rotation::cur());
                

                vec![
                    (it, table_config.tag),
                    (ita, table_config.table),
                    (is, table_config.spread),
                ]
            });
            meta.lookup("Spread Table 2", |meta| {

                let sd_abc = meta.query_selector(compression_chip.sd_abc.s_abc);
                let sd_efg = meta.query_selector(compression_chip.sd_efg.s_efg);
                let ita2 = meta.query_advice(cols[7], Rotation::cur());
                let is2 = meta.query_advice(cols[8], Rotation::cur());

                let flag = sd_abc.clone() + sd_efg.clone() + sd_abc * sd_efg;
                

                vec![
                    (flag.clone() * ita2, table_config.table),
                    (flag * is2, table_config.spread),
                ]
            });


            Self {
                table_config,
                compression_chip,
                message_schedule_chip
            }

        }

        pub fn assign(
            &self,
            mut layouter: impl Layouter<F>,
            w: Vec<u16>,
        ) -> Result<Vec<u32>, Error> {
            let k = [   
                0x428a2f98u32, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
                0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
                0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
                0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
                0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
            ].into_iter().fold(vec![], |mut l, elem| {
                l.push(elem as u16);
                l.push((elem >> 16) as u16);
                l
            });

            let h = [
                0x6a09e667u32,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x510e527f,
                0x9b05688c,
                0x1f83d9ab,
                0x5be0cd19
            ].into_iter().fold(vec![], |mut l, elem| {
                l.push(elem as u16);
                l.push((elem >> 16) as u16);
                l
            });

            layouter.assign_region(
                || "Single Round SHA256", 
                |mut region| {
                    let k = k.clone();
                    let w = w.clone();
                    let h = h.clone();
                    let (w_val, w_c) = self.message_schedule_chip.load(&mut region, w, 0)?;
                    let (h_val, _) = self.compression_chip.load(&mut region, w_c, w_val, k, h, 547)?;
                    let mut hash = vec![];
                    for i in 0..8 {
                        hash.push( h_val[2*i] as u32 + h_val[2*i+1] as u32 * ( 1 << 16) );
                    }
                    
                    Ok(hash)
                }
            )
        }
    }

    #[derive(Default, Clone)]
    struct SimpleCircuit<F: FieldExt, const NUM_BITS: usize> {
        w: Vec<u16>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt, const NUM_BITS: usize> Circuit<F> for SimpleCircuit<F, NUM_BITS> {
        type Config = SimpleConfig<F, NUM_BITS>;
        type FloorPlanner = SimpleFloorPlanner;
        
        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            SimpleConfig::configure(meta)
        }

        fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
            config.table_config.load(&mut layouter)?;
            let hash = config.assign(
                layouter, 
                self.w.clone(),
            )?;
            print!("{:?}", hash);
            Ok(())
        }
    }

    #[test]
    fn test_compression_circuit() {
        let mut input: Vec<u8> = "".as_bytes().to_vec();
        let l: u64 = input.len() as u64;
        
        let coef = (l+1+8) / 64;
        let rem = (l+1+8) % 64;
        let size = coef * 64 + (rem > 0) as u64 * 64;
        let num_zeros = size - input.len() as u64 - 1 - 8;
        
        input.extend([0x80]);
        input.extend(vec![0; num_zeros as usize]);
        input.extend((l*8).to_be_bytes());
        let mut w: Vec<u16> = vec![];
        for i in 0..input.len()/4 {
            w.push( input[4*i+3] as u16 + (input[4*i+2] as u16) * ( 1 << 8) );
            w.push( input[4*i+1] as u16 + (input[4*i+0] as u16) * ( 1 << 8) );
        }
        let circuit = SimpleCircuit::<F, 16> {
            w,
            _marker: PhantomData
        };
        
        let k = 17;
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        

    }


}