#![allow(unused)]

use halo2_proofs::{
    arithmetic::FieldExt,
    plonk::Expression,
};

pub fn and<F: FieldExt>(lhe: Expression<F>, rhe: Expression<F>) -> Expression<F> {
    lhe * rhe
}

pub fn eq<F: FieldExt>(lhe: Expression<F>, rhe: Expression<F>) -> Expression<F> {
    lhe - rhe
}

pub fn not<F: FieldExt>(e: Expression<F>) -> Expression<F> {
    Expression::Constant(F::one()) - e 
}

pub fn is_bool<F: FieldExt>(e: Expression<F>) -> Expression<F> {
    e.clone() * (e - Expression::Constant(F::one()))
}

// A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
pub fn xif<F: FieldExt>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    and(a, not(b))
}

pub fn fstr<F:FieldExt>(n: &F) -> String {
    let s = format!("{n:?}");
    if let Some(mut hex ) = s.strip_prefix("0x") {
        while hex.len() > 1 && hex.starts_with('0') {
            hex = &hex[1..];
        }
        if hex.len() < 8 {
            format!("{}",u64::from_str_radix(hex, 16).unwrap())
        } else {
            format!("0x{hex:}")
        }
    } else {
        s
    }
}

pub fn eval_expr<F :FieldExt>(expr: Expression<F>) -> F {
    expr.evaluate(
        &|c| c, 
        &|_| unimplemented!(), 
        &|_| unimplemented!(),
        &|_| unimplemented!(),
        &|_| unimplemented!(),
        &|_| unimplemented!(),
        &|v| F::zero()-v,
        &|a,b| a+b,
        &|a,b| a*b,
        &|a,b| a*b
    )
}