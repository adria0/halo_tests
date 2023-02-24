/*
The last problem is that we can check values that does not exist.
We have to check that the input n exists in the table.

+ Create a new valid_n column with valid n values
+ Lookup if exists (n, valid_n) value

We convert i into a Fixed column
*/

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
        TableColumn,
    },
    poly::Rotation,
};

mod is_zero;
mod util;

use is_zero::{IsZeroChip, IsZeroConfig};
use util::*;

#[derive(Default, Debug, Clone)]
struct FibCircuit<F: FieldExt> {
    max_n: usize,
    n: F,
    fib: F,
}

#[derive(Debug, Clone)]
struct FibCircuitConfig<F: FieldExt> {
    // this is the column where values are exposed
    instance: Column<Instance>,

    // n and fib are the same in all rows
    input_n: Column<Advice>,
    input_fib: Column<Advice>,

    // the fib computation
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,

    // counter of fib no
    i: Column<Fixed>,

    sel_all_rows: Selector,
    sel_not_last_row: Selector,

    i_less_n_is_zero: IsZeroConfig<F>,
    c_less_fib_is_zero: IsZeroConfig<F>,

    // Is exactly the same that i column, but API does not allow to use it a as a column
    valid_n: TableColumn,
}

impl<F: FieldExt> Circuit<F> for FibCircuit<F> {
    type Config = FibCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let one = Expression::Constant(F::one());

        let instance = meta.instance_column();

        let [a, b, c, input_n, input_fib] = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];

        let i = meta.fixed_column();
        let valid_n = meta.lookup_table_column();

        meta.enable_equality(input_n);
        meta.enable_equality(input_fib);
        meta.enable_equality(instance);

        let sel_all_rows = meta.selector();
        let q_all_rows = Expression::Selector(sel_all_rows);

        meta.create_gate("a[_]+b[_]=c[_]", |meta| {
            let a0 = meta.query_advice(a, Rotation::cur());
            let b0 = meta.query_advice(b, Rotation::cur());
            let c0 = meta.query_advice(c, Rotation::cur());
            [and(q_all_rows.clone(), eq(a0 + b0, c0))]
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
                and(q_not_last_row.clone(), eq(b1, c0)),
            ]
        });

        meta.create_gate("n equal", |meta| {
            let n0 = meta.query_advice(input_n, Rotation::cur());
            let n1 = meta.query_advice(input_n, Rotation::next());
            [q_not_last_row.clone() * (n1 - n0)]
        });

        meta.create_gate("fib equal", |meta| {
            let fib0 = meta.query_advice(input_n, Rotation::cur());
            let fib1 = meta.query_advice(input_n, Rotation::next());
            [q_not_last_row.clone() * (fib1 - fib0)]
        });

        meta.create_gate("i increasing", |meta| {
            let i0 = meta.query_fixed(i, Rotation::cur());
            let i1 = meta.query_fixed(i, Rotation::next());
            [q_not_last_row.clone() * ((i0 + one) - i1)]
        });

        let value_inv_1 = meta.advice_column();
        let value_inv_2 = meta.advice_column();
        let i_less_n_is_zero = IsZeroChip::configure(
            meta,
            |_| q_all_rows.clone(),
            |meta| {
                let i = meta.query_fixed(i, Rotation::cur());
                let input_n = meta.query_advice(input_n, Rotation::cur());
                i - input_n
            },
            value_inv_1,
        );

        let c_less_fib_is_zero = IsZeroChip::configure(
            meta,
            |_| q_all_rows.clone(),
            |meta| {
                let c = meta.query_advice(c, Rotation::cur());
                let input_fib = meta.query_advice(input_fib, Rotation::cur());
                c - input_fib
            },
            value_inv_2,
        );

        meta.create_gate("i == n, then c == fib ", |_| {
            [and(
                q_all_rows,
                xif(i_less_n_is_zero.expr(), c_less_fib_is_zero.expr()),
            )]
        });

        meta.lookup("input_n exists in valid_n", |meta| {
            let n = meta.query_any(input_n, Rotation::cur());
            vec![(n, valid_n)]
        });

        Self::Config {
            instance,
            a,
            b,
            c,
            i,
            valid_n,
            input_fib,
            input_n,
            sel_all_rows,
            sel_not_last_row,
            i_less_n_is_zero,
            c_less_fib_is_zero,
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
                let c_less_fib_is_zero_chip =
                    IsZeroChip::construct(config.c_less_fib_is_zero.clone());

                for (name, column) in [
                    ("a column", config.a),
                    ("b column", config.b),
                    ("c column", config.c),
                    ("n column", config.input_n),
                    ("fib column", config.input_fib),
                ] {
                    region.name_column(|| name, column);
                }
                region.name_column(|| "i column", config.i);

                let mut a = F::one();
                let mut b = F::one();
                let mut i = F::from(3);
                let mut offset = 0;

                let mut n_cell = None;
                let mut fib_cell = None;

                while offset <= self.max_n {
                    config.sel_all_rows.enable(&mut region, offset)?;

                    let n_cell_1 = region.assign_advice(
                        || "",
                        config.input_n,
                        offset,
                        || Value::known(self.n),
                    )?;

                    let fib_cell_1 = region.assign_advice(
                        || "",
                        config.input_fib,
                        offset,
                        || Value::known(self.fib),
                    )?;

                    if n_cell.is_none() && fib_cell.is_none() {
                        n_cell = Some(n_cell_1.cell());
                        fib_cell = Some(fib_cell_1.cell());
                    }

                    if offset < self.max_n {
                        config.sel_not_last_row.enable(&mut region, offset)?;
                    }

                    let c = a + b;

                    for (column, val) in [(config.a, a), (config.b, b), (config.c, c)] {
                        region.assign_advice(|| "", column, offset, || Value::known(val))?;
                    }

                    region.assign_fixed(|| "", config.i, offset, || Value::known(i))?;

                    i_less_n_is_zero_chip.assign(&mut region, offset, Value::known(i - self.n))?;
                    c_less_fib_is_zero_chip.assign(
                        &mut region,
                        offset,
                        Value::known(c - self.fib),
                    )?;

                    a = b;
                    b = c;

                    i += F::one();
                    offset += 1;
                }

                Ok((n_cell.unwrap(), fib_cell.unwrap()))
            },
        )?;

        layouter.assign_table(
            || "",
            |mut table| {
                for offset in 0..self.max_n {
                    table.assign_cell(
                        || "",
                        config.valid_n,
                        offset,
                        || Value::known(F::from(offset as u64 + 3)),
                    )?;
                }
                Ok(())
            },
        )?;

        layouter.constrain_instance(n_cell, config.instance, 0)?;
        layouter.constrain_instance(fib_cell, config.instance, 1)?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};

    #[test]
    fn test_fib() {
        assert!(do_test(6, 8), "valid fibonacci");
        assert!(do_test(5, 5), "valid fibonacci");
        assert!(!do_test(4, 5), "invalid fibonacci");
        assert!(!do_test(1, 5), "n=1 is not generated");
        assert!(!do_test(10001, 5), "n=1 is not generated");
    }

    fn do_test(n: u64, fib: u64) -> bool {
        let k = 4u32;
        const NUM_BLINDING_ROWS: usize = 7;

        let circuit = FibCircuit {
            max_n: 2usize.pow(k) - NUM_BLINDING_ROWS,
            n: Fr::from(n),
            fib: Fr::from(fib),
        };
        let public_inputs = vec![circuit.n, circuit.fib];
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();

        prover.verify().is_ok()
    }
}

fn main() {}
