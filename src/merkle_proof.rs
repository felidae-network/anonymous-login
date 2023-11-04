/// Starting with + operation
/// Ultimately + will be replaced by Hash operation
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct MerkleConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct MerkleChip<F: FieldExt> {
    config: MerkleConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> MerkleChip<F> {
    pub fn construct(config: MerkleConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MerkleConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        MerkleConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
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
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire table",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let mut a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0,
                )?;

                let mut b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0,
                )?;

                let mut c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;
                for row in 1..nrows {
                    self.config.selector.enable(&mut region, row)?;
                    // Copy the value from c in previous row to a in current row
                    a_cell = c_cell.copy_advice(|| "a", &mut region, self.config.col_a, row)?;

                    b_cell = region.assign_advice_from_instance(
                        || "b",
                        self.config.instance,
                        row + 1,
                        self.config.col_b,
                        row,
                    )?;

                    c_cell = region.assign_advice(
                        || "c",
                        self.config.col_c,
                        row,
                        || a_cell.value().copied() + b_cell.value(),
                    )?;
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
struct MyCircuit<F>(PhantomData<F>);

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = MerkleConfig;
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

        let c_cell = chip.assign(layouter.namespace(|| "entire table 1"), 3)?;

        chip.expose_public(layouter.namespace(|| "out"), &c_cell, 4)?;

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

        let circuit = MyCircuit(PhantomData);

        let public_input = vec![a, b, c, d, out];

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

        let circuit = MyCircuit(PhantomData);

        let public_input = vec![a, b, c, d, out];

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

        let circuit = MyCircuit::<Fp>(PhantomData);
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }
}
