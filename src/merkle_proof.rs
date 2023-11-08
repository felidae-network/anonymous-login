use crate::gadgets::is_zero::{IsZeroChip, IsZeroConfig};
/// Starting with + operation
/// Ultimately + will be replaced by Hash operation
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;
#[derive(Debug, Clone)]
struct MerkleConfig<F> {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
    pub is_zero: IsZeroConfig<F>,
}

#[derive(Debug, Clone)]
struct MerkleChip<F: FieldExt> {
    config: MerkleConfig<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MerkleChip<F> {
    pub fn construct(config: MerkleConfig<F>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MerkleConfig<F> {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        let value_inv = meta.advice_column();
        let is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(col_b, Rotation::cur()),
            value_inv,
        );

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("c = if b == 0 { a } else { a + b }", |meta| {
            //
            // col_a | col_b | col_c | selector | instance
            //   a      b        c       s            i
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![
                s.clone() * is_zero.expr() * (a.clone() - c.clone()),
                s * (Expression::Constant(F::one()) - is_zero.expr()) * (a + b - c),
            ]
        });

        MerkleConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
            is_zero,
        }
    }
    //                36
    //            /      \
    //       10              26
    //     /   \            /  \
    //   3       7       11      15
    //  / \     / \     / \     / \
    // 1   2   3   4   5   6   7   8
    // to prove the membership of 1 the path is 1, 2, 7, 26
    //
    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        inputs: Vec<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire table, c = if b==0 {a} else {a+b}",
            |mut region| {
                let is_zero_chip = IsZeroChip::construct(self.config.is_zero.clone());

                self.config.selector.enable(&mut region, 0)?;

                let mut a_cell = region.assign_advice_from_instance(

                    || "a",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;

                // b = 0; // in first row
                let mut b_cell = region.assign_advice(
                    || "b",

                    self.config.col_b,
                    0,
                    || Value::known(F::zero()),
                )?;

                let mut c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied(),
                )?;
                is_zero_chip.assign(&mut region, 0, b_cell.value().copied())?;
                // last element is the root element
                for row in 1..(inputs.len() - 1) {
                    self.config.selector.enable(&mut region, row)?;

                    // Copy the value from c in previous row to a in current row
                    a_cell = c_cell.copy_advice(|| "a", &mut region, self.config.col_a, row)?;

                    b_cell = region.assign_advice_from_instance(
                        || "b",
                        self.config.instance,

                        row,
                        self.config.col_b,
                        row,
                    )?;
                    is_zero_chip.assign(&mut region, row, b_cell.value().copied())?;

                    let value = if inputs[row] == F::zero() {
                        a_cell.value().copied()
                    } else {
                        a_cell.value().copied() + b_cell.value()
                    };

                    c_cell = region.assign_advice(|| "c", self.config.col_c, row, || value)?;

                }
                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F> {
    inputs: Vec<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = MerkleConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MerkleChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = MerkleChip::construct(config);


        let c_cell = chip.assign(layouter.namespace(|| "entire table 1"), self.inputs.clone())?;
        //last element in the input is the root hash
        chip.expose_public(layouter.namespace(|| "out"), &c_cell, self.inputs.len() - 1)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::marker::PhantomData;

    use super::MyCircuit;
    use halo2_proofs::{dev::MockProver, pasta::Fp};

    #[test]
    fn merkle_example1() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(2); // F[1]
        let c = Fp::from(7); // F[2]
        let d = Fp::from(26); // F[3]
        let out = Fp::from(36); // F[4]

        let public_input = vec![a, b, c, d, out];
        let circuit = MyCircuit {
            inputs: public_input.clone(),
        };

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();
        // or
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn merkle_example_smaller() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(2); // F[1]
        let c = Fp::from(7); // F[2]
        let out = Fp::from(10); // F[3]

        let public_input = vec![a, b, c, out];
        let circuit = MyCircuit {
            inputs: public_input.clone(),
        };


        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
        prover.assert_satisfied();
        // or
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn merkle_example_fails_on_wrong_root() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(2); // F[1]
        let c = Fp::from(7); // F[2]
        let d = Fp::from(26); // F[3]
        let out = Fp::from(37); // F[4]     // correct is 36

        let public_input = vec![a, b, c, d, out];
        let circuit = MyCircuit {
            inputs: public_input.clone(),
        };

        let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();


        assert_ne!(prover.verify(), Ok(()));
        //TODO! match the exact error
    }

    #[cfg(feature = "dev-graph")]
    #[test]
    fn plot_merkle1() {
        use plotters::prelude::*;

        let root = BitMapBackend::new("merkle-1-layout.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("Merkle 1 Layout", ("sans-serif", 60)).unwrap();
        let a = Fp::from(1); // F[0]
        let b = Fp::from(2); // F[1]
        let c = Fp::from(7); // F[2]
        let d = Fp::from(26); // F[3]
        let out = Fp::from(36); // F[4]

        let public_input = vec![a, b, c, d, out];
        let circuit = MyCircuit::<Fp> {
            inputs: public_input,
        };
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
