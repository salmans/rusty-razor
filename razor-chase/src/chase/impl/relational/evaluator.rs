//! A chase step over database models.
use super::{
    model::RelModel,
    sequent::{Attribute, Branch, Function, RelSequent, SymbolicAtom},
};
use crate::chase::{Admission, Bounder, EvaluateResult, Evaluator, Strategy, E};
use either::Either;

/// Evaluates sequents in [`RelModel`]s: a sequent with a single disjunct fires on each of its
/// current triggers in turn, skipping those that an earlier firing in the same step already
/// satisfied; a disjunctive sequent fires on one trigger and forks the model
/// once per disjunct. A bounder's [`Admission::Reuse`] is controlled reuse.
#[derive(Clone, Copy, Debug, Default)]
pub struct RelEvaluator;

impl<'s, Stg: Strategy<&'s RelSequent>> Evaluator<'s, Stg> for RelEvaluator {
    type Sequent = RelSequent;
    type Model = RelModel;

    fn evaluate<B: Bounder + ?Sized>(
        &self,
        model: &Self::Model,
        strategy: &mut Stg,
        bound: &B,
    ) -> Option<EvaluateResult<Self::Model>> {
        let found = strategy.find_map(|s| {
            let triggers = model.evaluate_view(&s.triggers).into_tuples();
            (!triggers.is_empty()).then_some((s, triggers))
        });
        let Some((sequent, triggers)) = found else {
            return Some(EvaluateResult::new());
        };
        if sequent.branches.is_empty() {
            return None; // the chase fails on this model
        }

        let mut result = EvaluateResult::new();
        let fired = sequent.firing(&triggers);
        for branch in &sequent.branches {
            let mut next = model.clone();
            for (i, env) in fired.iter().enumerate() {
                // A disjunct that creates elements may already have witnessed a later
                // trigger; firing it again would create a redundant element.
                if i > 0 && branch.creates_elements() && !next.contains(&sequent.triggers, env) {
                    continue;
                }
                info!(event = crate::trace::EVALUATE, sequent = %sequent, mapping = ?env);
                Balance::balance(&mut next, branch, env, bound);
            }
            result.append(settle(next, bound));
        }
        Some(result)
    }
}

/// Sorts a model a step produced: an open extension, or a bounded one when an element of the
/// finished model lies beyond `bound`. Only the finished model decides, since a later merge may
/// identify an over-bound element with one inside the bound.
fn settle<B: Bounder + ?Sized>(model: RelModel, bound: &B) -> Either<RelModel, RelModel> {
    if model.exceeds(bound) {
        Either::Right(model)
    } else {
        Either::Left(model)
    }
}

/// The state of balancing one disjunct in a model for one trigger.
struct Balance<'a, B: Bounder + ?Sized> {
    model: &'a mut RelModel,
    env: &'a [E],
    bound: &'a B,
    /// The elements of the disjunct's existentials, as they become known.
    exist: Vec<Option<E>>,
}

impl<'a, B: Bounder + ?Sized> Balance<'a, B> {
    fn known(&self, attr: &Attribute) -> bool {
        match attr {
            Attribute::Body(_) => true,
            Attribute::Exist(j) => self.exist[*j].is_some(),
        }
    }

    fn resolve(&self, attr: Attribute) -> E {
        let e = match attr {
            Attribute::Body(i) => self.env[i],
            Attribute::Exist(j) => self.exist[j].expect("existential used before it is produced"),
        };
        self.model.canon(e)
    }

    fn resolve_all(&self, attrs: &[Attribute]) -> Vec<E> {
        attrs.iter().map(|a| self.resolve(*a)).collect()
    }

    /// Makes `branch` true in `model` for the trigger `env`. An atom is balanced as soon as its
    /// inputs are known. A function application whose output is still unknown takes the
    /// model's value first if the model already defines it; only when nothing else can make
    /// progress is a new element created. This keeps the number of fresh elements, and of
    /// merges, to the minimum the disjunct requires.
    fn balance(model: &'a mut RelModel, branch: &Branch, env: &'a [E], bound: &'a B) {
        let mut state = Balance {
            model,
            env,
            bound,
            exist: vec![None; branch.existential_count],
        };
        let mut pending: Vec<&SymbolicAtom> = branch.atoms.iter().collect();
        while !pending.is_empty() {
            let mut progress = false;
            let mut deferred: Vec<&SymbolicAtom> = Vec::new();
            let mut creatable: Option<usize> = None;
            for atom in pending.drain(..) {
                match atom {
                    SymbolicAtom::Function {
                        function,
                        args,
                        out,
                    } if args.iter().all(|a| state.known(a)) => {
                        let args = state.resolve_all(args);
                        match out {
                            Attribute::Exist(j) if state.exist[*j].is_none() => {
                                if let Some(e) = state.model.lookup(function.symbol(), &args) {
                                    state.exist[*j] = Some(e);
                                    progress = true;
                                } else {
                                    creatable.get_or_insert(deferred.len());
                                    deferred.push(atom);
                                }
                            }
                            _ => {
                                let out = state.resolve(*out);
                                state.record(function, args, out);
                                progress = true;
                            }
                        }
                    }
                    SymbolicAtom::Relation { symbol, args }
                        if args.iter().all(|a| state.known(a)) =>
                    {
                        let tuple = state.resolve_all(args);
                        state.model.insert_fact(symbol, tuple);
                        progress = true;
                    }
                    SymbolicAtom::Equation(a, b) if state.known(a) && state.known(b) => {
                        let (a, b) = (state.resolve(*a), state.resolve(*b));
                        state.model.merge(a, b);
                        progress = true;
                    }
                    _ => deferred.push(atom),
                }
            }
            if !progress {
                let i = creatable.expect("an atom of a head can never be balanced");
                let SymbolicAtom::Function {
                    function,
                    args,
                    out: Attribute::Exist(j),
                } = deferred.remove(i)
                else {
                    unreachable!()
                };
                let args = state.resolve_all(args);
                let e = state.create(&args);
                state.record(function, args, e);
                state.exist[*j] = Some(e);
            }
            pending = deferred;
        }
    }

    /// Records `function(args) = out`: a fact for a function of the database, only a name for a
    /// witness.
    fn record(&mut self, function: &Function, args: Vec<E>, out: E) {
        match function {
            Function::Symbol(symbol) => self.model.define(symbol, args, out),
            Function::Witness(witness) => self.model.name(witness, args, out),
        }
    }

    /// Creates (or, under controlled reuse, picks) the element denoted by a function on `args`.
    /// An element beyond the bound is created all the same; [`settle`] reports the model.
    fn create(&mut self, args: &[E]) -> E {
        let model = &mut *self.model;
        let depth = model.depth(args);
        match self.bound.admit(model.size(), depth) {
            Admission::Create | Admission::Overflow => model.new_element(depth),
            Admission::Reuse => *args
                .iter()
                .max_by_key(|a| model.info(**a).depth)
                .expect("a term deeper than zero has arguments"),
        }
    }
}
