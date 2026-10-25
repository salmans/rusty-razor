//! Turns a first-order theory into compiled sequents and an empty model.
use super::{model::RelModel, sequent::RelSequent};
use crate::chase::{PreProcessor, Witnesses};
use razor_fol::{
    syntax::{Formula, Theory, FOF},
    transform::{Geometrization, Symbols, ToGNF, GNF},
};

/// Converts a theory to geometric sequents and compiles every one.
///
/// The conversion keeps an existential in a head wherever its scope allows, and removes it by
/// the pre-processor's [`Geometrization`] otherwise; an introduced symbol is an ordinary symbol
/// of the theory. Every theory is converted with fresh [`Symbols`], which name the introduced
/// symbols of the whole theory, and each compiled sequent records the witnesses of its head
/// existentials.
///
/// The default policy is [`Geometrization::Hybrid`], which terminates wherever Skolemization
/// does and never needs a totality claim.
#[derive(Clone, Copy, Debug, Default)]
pub struct RelPreProcessor {
    geometrization: Geometrization,
}

impl RelPreProcessor {
    /// A pre-processor that removes existentials by `geometrization`.
    pub fn new(geometrization: Geometrization) -> Self {
        Self { geometrization }
    }
}

impl PreProcessor for RelPreProcessor {
    type Sequent = RelSequent;
    type Model = RelModel;

    fn pre_process(&self, theory: &Theory<FOF>) -> (Vec<Self::Sequent>, Self::Model) {
        let mut symbols = Symbols::default();
        let gnfs: Theory<GNF> = theory
            .iter()
            .flat_map(|f| f.gnf_with(self.geometrization, &mut symbols))
            .collect();
        let signature = gnfs.signature().expect("invalid theory signature");
        let mut model = RelModel::new(&signature);
        let mut witnesses = Witnesses::new(&symbols);
        let sequents = gnfs
            .formulae()
            .iter()
            .filter_map(|sequent| {
                RelSequent::compile(sequent, model.database_mut(), &mut witnesses)
            })
            .collect();
        (sequents, model)
    }
}
