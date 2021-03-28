use super::{constants::*, expression::Convertor, model::RelModel, sequent::RelSequent};
use crate::chase::PreProcessor;
use itertools::Itertools;
use razor_fol::{
    syntax::{formula::*, term::Complex, Sig, Theory, Var, FOF},
    transform::{PcfSet, GNF, PCF},
};

/// Is a [`PreProcessor`] instance that converts the input theory to a vector of [`Sequent`].
/// This is done by the standard conversion to geometric normal form followed by relationalization.
/// The empty [`Model`] instance is created by adding all signature symbols to its underlying database.
///
/// [`Sequent`]: crate::chase::impl::relational::RelSequent
/// [`Model`]: crate::chase::impl::relational::RelModel
/// [`PreProcessor`]: crate::chase::PreProcessor
pub struct RelPreProcessor {
    memoize: bool,
}

impl RelPreProcessor {
    pub fn new(memoize: bool) -> Self {
        Self { memoize }
    }
}

impl PreProcessor for RelPreProcessor {
    type Sequent = RelSequent;
    type Model = RelModel;

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
        use razor_fol::transform::ToGNF;
        use razor_fol::transform::ToSNF;

        let mut c_counter: u32 = 0;
        let mut f_counter: u32 = 0;
        let mut const_generator = || {
            let name = skolem_constant_name(c_counter);
            c_counter += 1;
            name.into()
        };
        let mut fn_generator = || {
            let name = skolem_function_name(f_counter);
            f_counter += 1;
            name.into()
        };
        let mut geo_theory: Theory<_> = theory
            .iter()
            .map(|f| f.snf_with(&mut const_generator, &mut fn_generator))
            .flat_map(|f| f.gnf())
            .collect();

        geo_theory.extend(equality_axioms());
        let sig = geo_theory.signature().expect("invalid theory signature");
        geo_theory.extend(integrity_axioms(&sig));

        let mut model = RelModel::new(&sig);
        let mut convertor = if self.memoize {
            Convertor::memoizing(model.database_mut())
        } else {
            Convertor::new()
        };

        let sequents = geo_theory
            .formulae()
            .iter()
            .map(|fmla| RelSequent::new(&fmla, &mut convertor).unwrap())
            .collect();

        (sequents, model)
    }
}

fn equality_axioms() -> Vec<GNF> {
    use razor_fol::{fof, transform::ToGNF};

    // reflexive (not needed - automatically added for new elements):
    // fof!(['|'] -> [(x) = (x)]),
    // symmetric (not needed):
    // fof!([(x) = (y)] -> [(y) = (x)]),
    // transitive:
    fof!({[(x) = (y)] & [(y) = (z)]} -> {(x) = (z)}).gnf()
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
