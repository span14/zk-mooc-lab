
use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::{Expression},
};

pub fn create_interleave_num(num: u32) -> u32 {
    let mut result = num;
    result = (result ^ (result << 8)) & 0x00ff00ff;
    result = (result ^ (result << 4)) & 0x0f0f0f0f;
    result = (result ^ (result << 2)) & 0x33333333;
    result = (result ^ (result << 1)) & 0x55555555;
    result
}

pub fn create_tag(num: u16) -> u64 {
    if (num >> 7) > 0 {
        if (num >> 10) > 0 {
            if (num >> 11) > 0 {
                if (num >> 13) > 0 {
                    if (num >> 14) > 0 {
                        return 5;
                    }
                    return 4;
                }
                return 3;
            }
            return 2;
        }
        return 1;
    }
    return 0;
}

pub fn create_range_2_check<F: FieldExt>(a: Expression<F>) -> Expression<F> {
    a.clone() * 
    (a.clone()-Expression::Constant(F::one())) * 
    (a.clone()-Expression::Constant(F::from(2))) * 
    (a-Expression::Constant(F::from(3)))
}

pub fn create_spread_2_check<F: FieldExt>(a: Expression<F>, s_a: Expression<F>) -> Expression<F> {
    Expression::Constant(-F::from(2)) * (a.clone()*a.clone()*a.clone()) + 
    Expression::Constant(F::from(9)) * (a.clone()*a.clone()) +
    Expression::Constant(-F::from(4)) * a - 
    Expression::Constant(F::from(3)) * s_a
}

pub fn create_range_3_check<F: FieldExt>(a: Expression<F>) -> Expression<F> {
    a.clone() * 
    (a.clone()-Expression::Constant(F::one())) * 
    (a.clone()-Expression::Constant(F::from(2))) * 
    (a.clone()-Expression::Constant(F::from(3))) * 
    (a.clone()-Expression::Constant(F::from(4))) *
    (a.clone()-Expression::Constant(F::from(5))) * 
    (a.clone()-Expression::Constant(F::from(6))) * 
    (a-Expression::Constant(F::from(7)))
}

pub fn create_spread_3_check<F: FieldExt>(a: Expression<F>, s_a: Expression<F>) -> Expression<F> {
    Expression::Constant(-F::from(2)) * (a.clone()*a.clone()*a.clone()*a.clone()*a.clone()*a.clone()*a.clone()) + 
    Expression::Constant(F::from(49)) * (a.clone()*a.clone()*a.clone()*a.clone()*a.clone()*a.clone()) +
    Expression::Constant(-F::from(473)) * (a.clone()*a.clone()*a.clone()*a.clone()*a.clone()) + 
    Expression::Constant(F::from(2275)) * (a.clone()*a.clone()*a.clone()*a.clone()) + 
    Expression::Constant(-F::from(5663)) * (a.clone()*a.clone()*a.clone()) + 
    Expression::Constant(F::from(6811)) * (a.clone()*a.clone()) + 
    Expression::Constant(-F::from(2952)) * a - 
    Expression::Constant(F::from(45)) * s_a
}

pub fn create_value_4_check<F: FieldExt>(a: Expression<F>) -> Expression<F> {
    a.clone() * 
    (a.clone()-Expression::Constant(F::one())) * 
    (a.clone()-Expression::Constant(F::from(2))) * 
    (a.clone()-Expression::Constant(F::from(3))) * 
    (a.clone()-Expression::Constant(F::from(4)))
}

pub fn create_value_2_check<F: FieldExt>(a: Expression<F>) -> Expression<F> {
    a.clone() * 
    (a-Expression::Constant(F::one()))
}

pub fn sigma0(w_lo: u16, w_hi: u16) -> (u16, u16) {
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);

    let w_n = w.rotate_right(7) ^ w.rotate_right(18) ^ (w >> 3);

    ((w_n % (1 << 16)) as u16, (w_n >> 16) as u16)
}

pub fn sigma1(w_lo: u16, w_hi: u16) -> (u16, u16) {
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);
    
    let w_n = w.rotate_right(17) ^ w.rotate_right(19) ^ (w >> 10);

    ((w_n % (1 << 16)) as u16, (w_n >> 16) as u16)
}


pub fn sigma0_r(w_lo: u16, w_hi: u16) -> (u32, u32){
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);

    let w_7 = w.rotate_right(7);
    let s_w_7_lo = create_interleave_num(w_7 % ( 1 << 16));
    let s_w_7_hi = create_interleave_num(w_7 >> 16);
    let w_18 = w.rotate_right(18);
    let s_w_18_lo = create_interleave_num(w_18 % ( 1 << 16));
    let s_w_18_hi = create_interleave_num(w_18 >> 16);
    let w_3 = w >> 3;
    let s_w_3_lo = create_interleave_num(w_3 % ( 1 << 16));
    let s_w_3_hi = create_interleave_num(w_3 >> 16);

    (s_w_7_lo + s_w_18_lo + s_w_3_lo, s_w_7_hi + s_w_18_hi + s_w_3_hi)

}

pub fn sigma1_r(w_lo: u16, w_hi: u16) -> (u32, u32){
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);

    let w_17 = w.rotate_right(17);
    let s_w_17_lo = create_interleave_num(w_17 % ( 1 << 16));
    let s_w_17_hi = create_interleave_num(w_17 >> 16);
    let w_19 = w.rotate_right(19);
    let s_w_19_lo = create_interleave_num(w_19 % ( 1 << 16));
    let s_w_19_hi = create_interleave_num(w_19 >> 16);
    let w_10 = w >> 10;
    let s_w_10_lo = create_interleave_num(w_10 % ( 1 << 16));
    let s_w_10_hi = create_interleave_num(w_10 >> 16);

    (s_w_17_lo + s_w_19_lo + s_w_10_lo, s_w_17_hi + s_w_19_hi + s_w_10_hi)
}

pub fn sum0(w_lo: u16, w_hi: u16) -> u32 {
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);
    let w_2 = w.rotate_right(2);
    let w_13 = w.rotate_right(13);
    let w_22 = w.rotate_right(22);
    w_2 ^ w_13 ^ w_22
}

pub fn sum1(w_lo: u16, w_hi: u16) -> u32 {
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);
    let w_6 = w.rotate_right(6);
    let w_11 = w.rotate_right(11);
    let w_25 = w.rotate_right(25);
    w_6 ^ w_11 ^ w_25
}


pub fn sum0_r(w_lo: u16, w_hi: u16) -> (u32, u32){
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);

    let w_2 = w.rotate_right(2);
    let s_w_2_lo = create_interleave_num(w_2 % ( 1 << 16));
    let s_w_2_hi = create_interleave_num(w_2 >> 16);
    let w_13 = w.rotate_right(13);
    let s_w_13_lo = create_interleave_num(w_13 % ( 1 << 16));
    let s_w_13_hi = create_interleave_num(w_13 >> 16);
    let w_22 = w.rotate_right(22);
    let s_w_22_lo = create_interleave_num(w_22 % ( 1 << 16));
    let s_w_22_hi = create_interleave_num(w_22 >> 16);

    (s_w_2_lo + s_w_13_lo + s_w_22_lo, s_w_2_hi + s_w_13_hi + s_w_22_hi)

}

pub fn sum1_r(w_lo: u16, w_hi: u16) -> (u32, u32){
    let w = w_lo as u32 + (w_hi as u32) * (1 << 16);

    let w_6 = w.rotate_right(6);
    let s_w_6_lo = create_interleave_num(w_6 % ( 1 << 16));
    let s_w_6_hi = create_interleave_num(w_6 >> 16);
    let w_11 = w.rotate_right(11);
    let s_w_11_lo = create_interleave_num(w_11 % ( 1 << 16));
    let s_w_11_hi = create_interleave_num(w_11 >> 16);
    let w_25 = w.rotate_right(25);
    let s_w_25_lo = create_interleave_num(w_25 % ( 1 << 16));
    let s_w_25_hi = create_interleave_num(w_25 >> 16);

    (s_w_6_lo + s_w_11_lo + s_w_25_lo, s_w_6_hi + s_w_11_hi + s_w_25_hi)

}


pub fn new_w(w_i_2: u32, w_i_7: u32, w_i_15: u32, w_i_16: u32) -> (u16, u16) {
    let s1 = w_i_2.rotate_right(17) ^ w_i_2.rotate_right(19) ^ (w_i_2 >> 10);
    let s0 = w_i_15.rotate_right(7) ^ w_i_15.rotate_right(18) ^ (w_i_15 >> 3);
    let w_n = s1 ^ w_i_7 ^ s0 ^ w_i_16;
    
    ((w_n % (1 << 16)) as u16, (w_n >> 16) as u16)
}

pub fn reduce2(v1: u32, v2: u32) -> (u16, u16, u64) {
    let w = 
        v1 as u64 +
        v2 as u64;
    
    ((w & 0xFFFF) as u16, ((w>>16) & 0xFFFF) as u16, w >> 32)
}

pub fn reduce3(v1: u32, v2: u32, v3: u32) -> (u16, u16, u64) {
    let w = 
        v1 as u64 +
        v2 as u64 +
        v3 as u64;
    
    ((w & 0xFFFF) as u16, ((w>>16) & 0xFFFF) as u16, w >> 32)
}

pub fn reduce4(v1: u32, v2: u32, v3: u32, v4: u32) -> (u32, u64) {
    let w = 
        v1 as u64 +
        v2 as u64 +
        v3 as u64 +
        v4 as u64;
    
    ((w & 0xFFFFFFFF) as u32, w >> 32)
}

pub fn reduce5(v1: u32, v2: u32, v3: u32, v4: u32, v5: u32) -> (u16, u16, u64) {
    let w = 
        v1 as u64 +
        v2 as u64 +
        v3 as u64 +
        v4 as u64 +
        v5 as u64;
    
    ((w & 0xFFFF) as u16, ((w>>16) & 0xFFFF) as u16, w >> 32)
}

pub fn even_bit(w: u32) -> u16 {
    let mut res: u32 = 0;
    for i in 0..16 {
        res += ((w >> (i*2)) & 1) * ( 1 << i);
    }
    res as u16
}

pub fn odd_bit(w: u32) -> u16 {
    let mut res: u32 = 0;
    for i in 0..16 {
        res += ((w >> (i*2+1)) & 1) * (1 << i);
    }
    res as u16
}

pub fn e_and_f(e_lo: u16, e_hi: u16, f_lo: u16, f_hi: u16) -> (u32, u32) {
    let s_e_lo = create_interleave_num(e_lo as u32);
    let s_e_hi = create_interleave_num(e_hi as u32);
    let s_f_lo = create_interleave_num(f_lo as u32);
    let s_f_hi = create_interleave_num(f_hi as u32);

    (s_e_lo + s_f_lo, s_e_hi + s_f_hi)
}

pub fn ne_and_g(e_lo: u16, e_hi: u16, g_lo: u16, g_hi: u16) -> (u16, u16) {
    let q_lo = (!e_lo) & g_lo;
    let q_hi = (!e_hi) & g_hi;
    (q_lo, q_hi)
}

pub fn ne_and_g_r(e_lo: u16, e_hi: u16, g_lo: u16, g_hi: u16) -> (u32, u32) {

    let s_ne_lo = create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(e_lo as u32);
    let s_ne_hi = create_interleave_num( (1 << 16) - 1 ) - create_interleave_num(e_hi as u32);
    let s_g_lo = create_interleave_num(g_lo as u32);
    let s_g_hi = create_interleave_num(g_hi as u32);

    (s_ne_lo + s_g_lo, s_ne_hi + s_g_hi)
}


pub fn choice(e_lo: u16, e_hi: u16, f_lo: u16, f_hi: u16, g_lo: u16, g_hi: u16) -> u32 {
    let e = e_lo as u32 + e_hi as u32 * (1 << 16);
    let f = f_lo as u32 + f_hi as u32 * (1 << 16);
    let g = g_lo as u32 + g_hi as u32 * (1 << 16);

    (e & f) ^ (!e & g)
}

pub fn maj(a_lo: u16, a_hi: u16, b_lo: u16, b_hi: u16, c_lo: u16, c_hi: u16) -> u32 {
    let a = a_lo as u32 + a_hi as u32 * (1 << 16);
    let b = b_lo as u32 + b_hi as u32 * (1 << 16);
    let c = c_lo as u32 + c_hi as u32 * (1 << 16);

    (a & b) ^ (a & c) ^ (b & c)
}

pub fn maj_r(a_lo: u16, a_hi: u16, b_lo: u16, b_hi: u16, c_lo: u16, c_hi: u16) -> (u32, u32) {

    let s_a_lo = create_interleave_num(a_lo as u32);
    let s_a_hi = create_interleave_num(a_hi as u32);

    let s_b_lo = create_interleave_num(b_lo as u32);
    let s_b_hi = create_interleave_num(b_hi as u32);

    let s_c_lo = create_interleave_num(c_lo as u32);
    let s_c_hi = create_interleave_num(c_hi as u32);

    (s_a_lo + s_b_lo + s_c_lo, s_a_hi + s_b_hi + s_c_hi)
}