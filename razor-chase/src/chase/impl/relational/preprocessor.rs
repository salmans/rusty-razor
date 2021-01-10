use super::{expression::Convertor, model::Model, sequent::Sequent};
use crate::chase::PreProcessorEx;
use itertools::Itertools;
use razor_fol::{
    syntax::{formula::*, term::Complex, Sig, Theory, Var, FOF},
    transform::{PcfSet, GNF, PCF},
};

/// Is a [`PreProcessorEx`] instance that converts the input theory to a vector of [`Sequent`].
/// This is done by the standard conversion to geometric normal form followed by relationalization.
/// The empty [`Model`] instance is created by adding all signature symbols to its underlying database.
///
/// [`Sequent`]: crate::chase::impl::relational::Sequent
/// [`Model`]: crate::chase::impl::relational::Model
/// [`PreProcessorEx`]: crate::chase::PreProcessorEx
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

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
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

fn equality_axioms() -> Vec<GNF> {
    use razor_fol::term;

    let x_y: Atomic<_> = Equals {
        left: term!(x),
        right: term!(y),
    }
    .into();
    let y_z: Atomic<_> = Equals {
        left: term!(y),
        right: term!(z),
    }
    .into();
    let x_z: Atomic<_> = Equals {
        left: term!(y),
        right: term!(z),
    }
    .into();

    let transitive: GNF = (PCF::from(vec![x_y, y_z]), PcfSet::from(PCF::from(x_z))).into();

    vec![
        // reflexive (not needed - automatically added for new elements):
        // fof!(['|'] -> [(x) = (x)]),
        // symmetric (not needed):
        // fof!([(x) = (y)] -> [(y) = (x)]),
        transitive,
    ]
}

// Function integrity axioms in the form of:
// 1) 'c = x & 'c = y -> x = y
// 2) (f(x1, ..., xn) = x) & (f(y1, ..., yn) = y) & x1 = y1 & ... & xn = yn -> x = y
fn integrity_axioms(sig: &Sig) -> Vec<GNF> {
    use razor_fol::term;

    let mut result = Vec::new();
    for c in sig.constants() {
        let c_x: Atomic<_> = Equals {
            left: c.clone().into(),
            right: term!(x),
        }
        .into();
        let c_y: Atomic<_> = Equals {
            left: c.clone().into(),
            right: term!(y),
        }
        .into();
        let x_y: Atomic<_> = Equals {
            left: term!(x),
            right: term!(y),
        }
        .into();

        let gnf: GNF = (PCF::from(vec![c_x, c_y]), PcfSet::from(PCF::from(x_y))).into();
        result.push(gnf);
    }

    for f in sig.functions().values() {
        let left = {
            let xs = (0..f.arity)
                .map(|n| Complex::from(Var::from(format!("x{}", n))))
                .collect_vec();
            let ys = (0..f.arity)
                .map(|n| Complex::from(Var::from(format!("y{}", n))))
                .collect_vec();

            let f_xs: Atomic<_> = Equals {
                left: f.symbol.clone().app(xs.clone()),
                right: term!(x),
            }
            .into();
            let f_ys: Atomic<_> = Equals {
                left: f.symbol.clone().app(ys.clone()),
                right: term!(y),
            }
            .into();

            let xs_ys = xs
                .into_iter()
                .zip(ys.into_iter())
                .map(|(x, y)| Atomic::from(Equals { left: x, right: y }));

            let mut atomics = Vec::new();
            atomics.push(f_xs);
            atomics.push(f_ys);
            atomics.extend(xs_ys);
            atomics
        };
        let right: Atomic<_> = Equals {
            left: term!(x),
            right: term!(y),
        }
        .into();

        let gnf: GNF = (PCF::from(left), PcfSet::from(PCF::from(right))).into();
        result.push(gnf);
    }

    result
}
