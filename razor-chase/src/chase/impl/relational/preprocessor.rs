use super::{expression::Convertor, model::Model, sequent::Sequent};
use crate::chase::PreProcessorEx;
use itertools::Itertools;
use razor_fol::syntax::{Formula, Sig, Term, Theory, V};

/// Is a [`PreProcessorEx`] instance that converts the input theory to a vector of [`Sequent`].
/// This is done by the standard conversion to geometric normal form followed by relationalization.
/// The empty [`Model`] instance is created by adding all signature symbols to its underlying database.
///
/// [`Sequent`]: ../sequent/struct.Sequent.html
/// [`Model`]: ../model/struct.Model.html
/// [`PreProcessorEx`]: ../../../trait.PreProcessorEx.html
pub struct PreProcessor {
    memoize: bool,
}

impl PreProcessor {
    pub fn new(memoize: bool) -> Self {
        Self { memoize }
    }
}

impl PreProcessorEx for PreProcessor {
    type Sequent = Sequent;
    type Model = Model;

    fn pre_process(&self, theory: &Theory) -> (Vec<Self::Sequent>, Self::Model) {
        let mut theory = theory.gnf();
        theory
            .extend(equality_axioms())
            .expect("failed to add equality axioms");
        theory
            .extend(integrity_axioms(theory.signature()))
            .expect("failed to add function integrity axioms");

        let mut model = Model::new(&theory.signature());
        let mut convertor = if self.memoize {
            Convertor::memoizing(model.database_mut())
        } else {
            Convertor::new()
        };

        let sequents = theory
            .formulae()
            .iter()
            .map(|fmla| Sequent::new(&fmla, &mut convertor).unwrap())
            .collect();

        (sequents, model)
    }
}

// Equality axioms:
fn equality_axioms() -> Vec<Formula> {
    use razor_fol::formula;

    vec![
        // formula!(['|'] -> [(x) = (x)]), // not needed: added automatically for new elements
        // formula!([(x) = (y)] -> [(y) = (x)]), // not needed
        formula!([{(x) = (y)} & {(y) = (z)}] -> [(x) = (z)]),
    ]
}

// Function integrity axioms in the form of:
// 1) 'c = x & 'c = y -> x = y
// 2) (f(x1, ..., xn) = x) & (f(y1, ..., yn) = y) & x1 = y1 & ... & xn = yn -> x = y
fn integrity_axioms(sig: &Sig) -> Vec<Formula> {
    let mut result = Vec::new();
    for c in sig.constants() {
        let x = Term::from(V("x".to_string()));
        let y = Term::from(V("y".to_string()));
        let c = Term::from(c.clone());

        let left = {
            let c_x = c.clone().equals(x.clone());
            let c_y = c.clone().equals(y.clone());
            c_x.and(c_y) // ('c = x) & ('c = y)
        };
        let right = x.equals(y); // x = y
        result.push(left.implies(right));
    }

    for f in sig.functions().values() {
        let x = Term::from(V("x".to_string()));
        let y = Term::from(V("y".to_string()));

        let left = {
            let xs = (0..f.arity)
                .map(|n| Term::from(V(format!("x{}", n))))
                .collect_vec();
            let ys = (0..f.arity)
                .map(|n| Term::from(V(format!("y{}", n))))
                .collect_vec();

            let f_xs = f.symbol.clone().app(xs.clone()).equals(x.clone());
            let f_ys = f.symbol.clone().app(ys.clone()).equals(y.clone());

            let xs_ys = xs.into_iter().zip(ys.into_iter()).map(|(x, y)| x.equals(y));

            xs_ys.fold(f_xs.and(f_ys), |fmla, eq| fmla.and(eq))
        };

        let right = x.equals(y); // x = y
        result.push(left.implies(right));
    }

    result
}
