//! Turns a first-order theory into compiled sequents and an empty model.
use super::{model::RelModel, sequent::RelSequent};
use crate::chase::PreProcessor;
use razor_fol::{
    syntax::{Formula, Theory, FOF},
    transform::{Skolemizer, GNF},
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
        let gnfs: Theory<GNF> = theory.iter().flat_map(|f| skolemizer.gnf(f)).collect();
        let signature = gnfs.signature().expect("invalid theory signature");
        let mut model = RelModel::new(&signature);
        let sequents = gnfs
            .formulae()
            .iter()
            .filter_map(|sequent| {
                RelSequent::compile(sequent, model.database_mut(), &mut skolemizer)
            })
            .collect();
        (sequents, model)
    }
}
