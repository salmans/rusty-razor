//! Turns a first-order theory into compiled sequents and an empty model.
use super::{model::RelModel, sequent::RelSequent};
use crate::chase::PreProcessor;
use razor_fol::{
    syntax::{Formula, Theory, FOF},
    transform::{Geometric, Skolemizer},
};

/// Converts a theory to geometric sequents and compiles every one.
///
/// The conversion keeps an existential in a head wherever its scope allows, and Skolemizes it
/// otherwise; a Skolem symbol is an ordinary function of the theory. One [`Skolemizer`] names the
/// Skolem symbols of the whole theory and then the witnesses the compiler mints for head
/// existentials, so no two symbols share a name.
#[derive(Clone, Debug, Default)]
pub struct RelPreProcessor;

impl PreProcessor for RelPreProcessor {
    type Sequent = RelSequent;
    type Model = RelModel;

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
        let mut skolemizer = Skolemizer::default();
        let geometric: Theory<Geometric> = theory
            .iter()
            .flat_map(|f| skolemizer.geometric(f))
            .collect();
        let signature = geometric.signature().expect("invalid theory signature");
        let mut model = RelModel::new(&signature);
        let sequents = geometric
            .formulae()
            .iter()
            .filter_map(|sequent| {
                RelSequent::compile(sequent, model.database_mut(), &mut skolemizer)
            })
            .collect();
        (sequents, model)
    }
}

#[cfg(test)]
mod tests {
    use super::super::{
        sequent::{Function, SymbolicAtom},
        Symbol,
    };
    use super::*;
    use razor_fol::syntax::{term::Complex, Const, Pred};

    #[test]
    fn a_user_constant_named_like_a_skolem_constant_is_a_function() {
        let fact = Pred::from("P").app(vec![Complex::from(Const::from("c#9"))]);
        let theory: Theory<FOF> = std::iter::once(FOF::from(fact)).collect();
        let (sequents, _) = RelPreProcessor.pre_process(&theory);
        assert!(matches!(
            &sequents[0].branches[0].atoms[0],
            SymbolicAtom::Function {
                function: Function::Symbol(Symbol::Const(c)),
                ..
            } if c.name() == "c#9"
        ));
    }
}
