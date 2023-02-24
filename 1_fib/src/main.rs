use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Instance, Selector,
    },
    poly::Rotation,
};

mod is_zero;
use is_zero::{IsZeroChip, IsZeroConfig};


fn and<F: FieldExt>(lhe: Expression<F>, rhe: Expression<F>) -> Expression<F> {
    lhe * rhe
}

fn eq<F: FieldExt>(lhe: Expression<F>, rhe: Expression<F>) -> Expression<F> {
    lhe - rhe
}

fn not<F: FieldExt>(e: Expression<F>) -> Expression<F> {
    Expression::Constant(F::one()) - e 
}

pub fn is_bool<F: FieldExt>(e: Expression<F>) -> Expression<F> {
    e.clone() * (e - Expression::Constant(F::one()))
}

// A=>B  eq ~(A & ~B) (it is not the case that A is true and B is false)
fn xif<F: FieldExt>(a: Expression<F>, b: Expression<F>) -> Expression<F> {
    and(a, not(b))
}

fn fstr<F:FieldExt>(n: &F) -> String {
    let s = format!("{:?}",n);
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

fn eval<F :FieldExt>(expr: Expression<F>) -> F {
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

#[derive(Default, Debug, Clone)]
struct FibCircuit<F: FieldExt> {
    max_n : usize,
    n : F,
    fib: F,
    // private witness data goes here
}

#[derive(Debug, Clone)]
struct FibCircuitConfig<F: FieldExt> {
    sel_all_rows: Selector,
    sel_not_last_row: Selector,
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    n: Column<Advice>,
    fib: Column<Advice>,
    i: Column<Advice>,
    instance: Column<Instance>,
    i_less_n_is_zero : IsZeroConfig<F>,
    c_less_fib_is_zero : IsZeroConfig<F>,
    // is_zero_2: IsZeroConfig<F>,
    _f: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for FibCircuit<F> {
    // Since we are using a single chip for everything, we can just reuse its config.
    type Config = FibCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    /*
      a   b   c  count I
      1   1   2  3     3
      1   2   3  2 .   5
      2   3   4  1
      3   4   5  0
    */

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let one = Expression::Constant(F::one());

        let instance = meta.instance_column();

        let [a, b, c,n,i, fib] = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        meta.enable_equality(n);
        meta.enable_equality(fib);
        meta.enable_equality(instance);

        let sel_all_rows = meta.selector();
        let q_all_rows = Expression::Selector(sel_all_rows);

        meta.create_gate("a[_]+b[_]=c[_]", |meta| {
            let a0 = meta.query_advice(a, Rotation::cur());
            let b0 = meta.query_advice(b, Rotation::cur());
            let c0 = meta.query_advice(c, Rotation::cur());
            [and(q_all_rows.clone(),eq(a0 + b0,c0))]
        });

        let sel_not_last_row = meta.selector();
        let q_not_last_row = Expression::Selector(sel_not_last_row);

        meta.create_gate("a[_+1] = b[_] ; b[_+1] = c[_]", |meta| {
            let b0 = meta.query_advice(b, Rotation::cur());
            let c0 = meta.query_advice(c, Rotation::cur());
            let a1 = meta.query_advice(a, Rotation::next());
            let b1 = meta.query_advice(b, Rotation::next());
            [
                and(q_not_last_row.clone(), eq(a1, b0)),
                and(q_not_last_row.clone(), eq(b1 ,c0)),
            ]
        });

        meta.create_gate("n equal", |meta| {
            let n0 = meta.query_advice(n, Rotation::cur());
            let n1 = meta.query_advice(n, Rotation::next());
            [q_not_last_row.clone() * (n1 - n0)]
        });

        meta.create_gate("fib equal", |meta| {
            let fib0 = meta.query_advice(n, Rotation::cur());
            let fib1 = meta.query_advice(n, Rotation::next());
            [q_not_last_row.clone() * (fib1 - fib0)]
        });

        meta.create_gate("i increasing", |meta| {
            let i0 = meta.query_advice(i, Rotation::cur());
            let i1 = meta.query_advice(i, Rotation::next());
            [q_not_last_row.clone() * ((i0 + one) - i1)]
        });


        let value_inv_1 = meta.advice_column();
        let value_inv_2 = meta.advice_column();
        let i_less_n_is_zero = IsZeroChip::configure(
            meta,
            |_| {
                q_not_last_row.clone()
            },
            |meta| {
                let i = meta.query_advice(i, Rotation::cur());
                let n = meta.query_advice(n, Rotation::cur());
                i - n
            },
            value_inv_1
        );

        let c_less_fib_is_zero = IsZeroChip::configure(
            meta,
            |_| {
                q_not_last_row
            },
            |meta| {
                let c = meta.query_advice(c, Rotation::cur());
                let fib = meta.query_advice(fib, Rotation::cur());
                c - fib
            },
            value_inv_2
        );

        meta.create_gate("i == n, then c == fib ", |_| {
            [and(q_all_rows,xif(i_less_n_is_zero.expr(), c_less_fib_is_zero.expr()))]
        });        

        Self::Config {
            a,
            b,
            c,
            i,
            fib,
            n,
            sel_all_rows,
            sel_not_last_row,
            instance,
            i_less_n_is_zero,
            c_less_fib_is_zero,
            _f: PhantomData::default(),
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {

        let (n_cell, fib_cell) = layouter.assign_region(
            || "region1",
            |mut region| {

                let i_less_n_is_zero_chip = IsZeroChip::construct(config.i_less_n_is_zero.clone());
                let c_less_fib_is_zero_chip  = IsZeroChip::construct(config.c_less_fib_is_zero.clone());

                region.name_column(|| "a column", config.a);
                region.name_column(|| "b column", config.b);
                region.name_column(|| "c column", config.c);
                region.name_column(|| "i column", config.i);
                region.name_column(|| "n column", config.n);
                region.name_column(|| "fib column", config.fib);

                let mut a = F::one();
                let mut b = F::one();
                let mut i = F::from(3);
                let mut offset = 0;

                let mut n_cell = None;
                let mut fib_cell = None;
                
                while offset <= self.max_n {

                    let c = a + b;

                    println!("i:{} n:{} a:{} b:{} c:{} fib:{}",fstr(&i),fstr(&self.n), fstr(&a),fstr(&b),fstr(&c), fstr(&self.fib)); 

                    config.sel_all_rows.enable(&mut region, offset)?;

                    n_cell = {
                        let cell = region.assign_advice(|| "", config.n, offset, || Value::known(self.n))?;
                        if offset == 0 {
                            Some(cell.cell())
                        } else {
                            n_cell
                        }
                    };                
                     fib_cell = {
                        let cell = region.assign_advice(|| "", config.fib, offset, || Value::known(self.fib))?;
                        if offset == 0 {
                            Some(cell.cell())
                        } else {
                            fib_cell
                        }
                    };                
                    
                    if offset  < self.max_n {
                        config.sel_not_last_row.enable(&mut region, offset)?;
                    }

                    for (column, val) in [(config.a, a), (config.b, b), (config.c, c), (config.i, i)] {
                        i_less_n_is_zero_chip.assign(&mut region, offset, Value::known(i - self.n) )?;
                        c_less_fib_is_zero_chip.assign(&mut region, offset, Value::known(c - self.fib) )?;
                        region.assign_advice(|| "", column, offset, || Value::known(val))?;
                    }

                    a = b;
                    b = c;

                    i += F::one();   
                    offset += 1;
                }
                
                Ok((n_cell.unwrap(), fib_cell.unwrap()))
            })?;

            layouter.constrain_instance(n_cell, config.instance, 0)?;
            layouter.constrain_instance(fib_cell, config.instance, 1)?;

        Ok(())
    }
}


fn main() {
    use halo2_proofs::{dev::MockProver,halo2curves::bn256::Fr};
    let circuit = FibCircuit { max_n : 3, n: Fr::from(4), fib: Fr::from(3)};
    let public_inputs = vec![Fr::from(4), Fr::from(3)];
    let prover = MockProver::run(4, &circuit, vec![public_inputs]).unwrap();
    prover.assert_satisfied();
}
