//! Cross-checks the relational chase against the basic implementation on the fixtures and on
//! random theories, as sets of support, and exercises the restricted chase and the bounds.
use super::{RelEvaluator, RelModel, RelPreProcessor};
use crate::{
    chase::{
        chase_step,
        r#impl::basic::{BasicEvaluator, BasicModel, BasicPreProcessor, BasicWitnessTerm},
        scheduler::FIFO,
        strategy::{Bootstrap, Fair, Linear},
        Bounder, Depth, DepthMode, DomainSize, Evaluator, Model, Observation, PreProcessor,
        Scheduler, Sequent, Strategy, Unbounded, E,
    },
    test_prelude::read_theory_from_file,
};
use razor_fol::syntax::{Const, Pred, Theory, EQ_SYM, FOF};
use std::collections::BTreeSet;

/// A model reduced to its structure over element indices.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Shape {
    size: usize,
    facts: BTreeSet<(String, Vec<usize>)>,
    functions: BTreeSet<(String, Vec<usize>, usize)>,
    constants: BTreeSet<(String, usize)>,
}

fn shape<M: Model<TermType = BasicWitnessTerm>>(model: &M) -> Shape {
    let domain = model.domain();
    let index = |e: &E| domain.iter().position(|d| d == e).unwrap();
    let mut facts = BTreeSet::new();
    for obs in model.facts() {
        if let Observation::Fact { relation, terms } = obs {
            let terms = terms
                .iter()
                .map(|t| match t {
                    BasicWitnessTerm::Elem(e) => index(e),
                    _ => panic!("non-element term in a fact"),
                })
                .collect();
            facts.insert((relation.to_string(), terms));
        }
    }
    let mut functions = BTreeSet::new();
    let mut constants = BTreeSet::new();
    for e in &domain {
        for w in model.witness(e) {
            match w {
                BasicWitnessTerm::Const(c) => {
                    constants.insert((c.name().to_string(), index(e)));
                }
                BasicWitnessTerm::App { function, terms } => {
                    let args = terms
                        .iter()
                        .map(|t| match t {
                            BasicWitnessTerm::Elem(a) => index(a),
                            _ => panic!("non-element argument in a witness"),
                        })
                        .collect();
                    functions.insert((function.name().to_string(), args, index(e)));
                }
                BasicWitnessTerm::Elem(_) => {}
            }
        }
    }
    Shape {
        size: domain.len(),
        facts,
        functions,
        constants,
    }
}

impl Shape {
    /// The number of facts of `relation`.
    fn count(&self, relation: &str) -> usize {
        self.facts.iter().filter(|(r, _)| r == relation).count()
    }
}

/// Chases `init` under `strategy` to the end, splitting complete models from bounded ones.
fn drain<'s, S, M, Stg, Ev, B>(
    init: M,
    strategy: Stg,
    evaluator: &Ev,
    bound: &B,
) -> (Vec<M>, Vec<M>)
where
    S: 's + Sequent,
    M: Model + std::fmt::Debug,
    Stg: Strategy<&'s S>,
    Ev: Evaluator<'s, Stg, Sequent = S, Model = M>,
    B: Bounder + ?Sized,
{
    let mut scheduler = FIFO::new();
    scheduler.add(init, strategy);
    let mut complete = Vec::new();
    let mut incomplete = Vec::new();
    while !scheduler.empty() {
        chase_step(
            &mut scheduler,
            evaluator,
            bound,
            |m| complete.push(m),
            |m| incomplete.push(m),
        );
    }
    (complete, incomplete)
}

fn run_basic(theory: &Theory<FOF>) -> Vec<BasicModel> {
    run_basic_bounded(theory, &Unbounded).0
}

fn run_basic_bounded<B: Bounder + ?Sized>(
    theory: &Theory<FOF>,
    bound: &B,
) -> (Vec<BasicModel>, Vec<BasicModel>) {
    let (sequents, init) = BasicPreProcessor.pre_process(theory);
    let strategy: Linear<_> = sequents.iter().collect();
    drain(init, strategy, &BasicEvaluator, bound)
}

fn run_db<B: Bounder + ?Sized>(theory: &Theory<FOF>, bound: &B) -> (Vec<RelModel>, Vec<RelModel>) {
    let (sequents, init) = RelPreProcessor.pre_process(theory);
    let strategy: Bootstrap<_, Fair<_>> = sequents.iter().collect();
    drain(init, strategy, &RelEvaluator, bound)
}

fn core_theories() -> Vec<(String, Theory<FOF>)> {
    let mut paths: Vec<_> = std::fs::read_dir("../theories/core")
        .unwrap()
        .map(|item| item.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "raz"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no fixtures found");
    paths
        .into_iter()
        .map(|p| {
            let name = p.file_stem().unwrap().to_string_lossy().into_owned();
            (name, read_theory_from_file(p.to_str().unwrap()))
        })
        .collect()
}

#[test]
fn restricted_chase_terminates_on_core_fixtures() {
    for (name, theory) in core_theories() {
        let (complete, incomplete) = run_db(&theory, &Unbounded);
        assert!(incomplete.is_empty(), "{}: incomplete models", name);
        let basic = run_basic(&theory);
        assert_eq!(
            basic.is_empty(),
            complete.is_empty(),
            "{}: satisfiability differs between the restricted chase and basic",
            name
        );
    }
}

#[test]
fn restricted_chase_skips_witnessed_existentials() {
    // Q(a, b) already witnesses the head for x = a, so no element is created.
    let theory: Theory<FOF> = "P('a); Q('a, 'b); P(x) -> exists y. Q(x, y);"
        .parse()
        .unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    assert_eq!(2, complete[0].size());
}

#[test]
fn depth_bound_with_reuse_gives_complete_models() {
    let theory: Theory<FOF> = "exists x. P(x); P(x) -> exists y. (R(x, y) & P(y));"
        .parse()
        .unwrap();
    let (complete, incomplete) = run_db(
        &theory,
        &Depth {
            max: 2,
            mode: DepthMode::Reuse,
        },
    );
    assert!(incomplete.is_empty());
    assert_eq!(1, complete.len());
    assert_eq!(3, complete[0].size());
    let (complete, incomplete) = run_db(
        &theory,
        &Depth {
            max: 2,
            mode: DepthMode::Pure,
        },
    );
    assert!(complete.is_empty());
    assert_eq!(1, incomplete.len());
}

#[test]
fn domain_bound_reports_incomplete_models() {
    let theory: Theory<FOF> = "exists x. P(x); P(x) -> exists y. (R(x, y) & P(y));"
        .parse()
        .unwrap();
    let (complete, incomplete) = run_db(&theory, &DomainSize(3));
    assert!(complete.is_empty());
    assert_eq!(1, incomplete.len());
    assert_eq!(4, incomplete[0].size());
}

#[test]
fn a_merged_away_overflow_does_not_bound_the_model() {
    // g('a) = h('b) overflows the bound, but h('c) = 'c then merges g('a) into 'c.
    let theory: Theory<FOF> = "P('a, 'b); P('a, 'c); h('c) = 'c; \
         forall x, y. (P(x, y) -> g(x) = h(y));"
        .parse()
        .unwrap();
    let (complete, incomplete) = run_db(&theory, &DomainSize(3));
    assert_eq!(1, complete.len(), "{:?}", incomplete);
    assert!(incomplete.is_empty(), "{:?}", incomplete);
    check_all("merged overflow", &theory, &complete);
}

#[test]
fn a_shallower_name_lowers_the_depth() {
    // The witness y of P('a) is named 'c, so the S-witness over it has depth 1, not 2.
    let theory: Theory<FOF> = "P('a); forall x. (P(x) -> exists y. Q(x, y)); \
         forall x, y. (Q(x, y) -> y = 'c); forall x, y. (Q(x, y) -> T(y)); \
         forall y. (T(y) -> exists z. S(y, z));"
        .parse()
        .unwrap();
    let pure = Depth {
        max: 1,
        mode: DepthMode::Pure,
    };
    let (complete, incomplete) = run_db(&theory, &pure);
    assert!(incomplete.is_empty(), "{:?}", incomplete);
    assert_eq!(1, complete.len());
    check_all("pure", &theory, &complete);
    let (complete, incomplete) = run_basic_bounded(&theory, &pure);
    assert!(incomplete.is_empty(), "basic: {:?}", incomplete);
    assert_eq!(1, complete.len());

    let reuse = Depth {
        max: 1,
        mode: DepthMode::Reuse,
    };
    let (complete, _) = run_db(&theory, &reuse);
    assert_eq!(1, complete.len());
    check_all("reuse", &theory, &complete);
    let s = shape(&complete[0]);
    assert_eq!(3, s.size, "{:?}", complete[0]);
    assert!(
        s.facts.iter().all(|(r, ts)| r != "S" || ts[0] != ts[1]),
        "{:?}",
        complete[0]
    );
}

// ---------------------------------------------------------------------------------------------
// Model checking: every model the engine returns must satisfy the original theory.
//
// Functions are partial in chase models, so an atom or equation mentioning an undefined term
// is false. Free variables of a sentence are read as universally quantified, as the conversion
// to geometric normal form does.

use razor_fol::syntax::{formula::*, term::Complex, Formula, Var};
use std::collections::HashMap;

fn eval_term(s: &Shape, t: &Complex, env: &HashMap<Var, usize>) -> Option<usize> {
    match t {
        Complex::Var(v) => env.get(v).copied(),
        Complex::Const(c) => s
            .constants
            .iter()
            .find(|(name, _)| name == c.name())
            .map(|(_, e)| *e),
        Complex::App { function, terms } => {
            let args: Option<Vec<usize>> = terms.iter().map(|t| eval_term(s, t, env)).collect();
            let args = args?;
            s.functions
                .iter()
                .find(|(name, a, _)| name == function.name() && *a == args)
                .map(|(_, _, out)| *out)
        }
    }
}

fn holds(s: &Shape, f: &FOF, env: &mut HashMap<Var, usize>) -> bool {
    match f {
        FOF::Top => true,
        FOF::Bottom => false,
        FOF::Atom(Atom { predicate, terms }) => {
            let args: Option<Vec<usize>> = terms.iter().map(|t| eval_term(s, t, env)).collect();
            args.is_some_and(|args| s.facts.contains(&(predicate.name().to_string(), args)))
        }
        FOF::Equals(Equals { left, right }) => {
            match (eval_term(s, left, env), eval_term(s, right, env)) {
                (Some(l), Some(r)) => l == r,
                _ => false,
            }
        }
        FOF::Not(n) => !holds(s, &n.formula, env),
        FOF::And(a) => holds(s, &a.left, env) && holds(s, &a.right, env),
        FOF::Or(o) => holds(s, &o.left, env) || holds(s, &o.right, env),
        FOF::Implies(i) => !holds(s, &i.premise, env) || holds(s, &i.consequence, env),
        FOF::Iff(i) => holds(s, &i.left, env) == holds(s, &i.right, env),
        FOF::Exists(e) => quantify(s, &e.variables, &e.formula, env, false),
        FOF::Forall(a) => quantify(s, &a.variables, &a.formula, env, true),
    }
}

fn quantify(s: &Shape, vars: &[Var], f: &FOF, env: &mut HashMap<Var, usize>, all: bool) -> bool {
    if vars.is_empty() {
        return holds(s, f, env);
    }
    for e in 0..s.size {
        let saved = env.insert(vars[0].clone(), e);
        let r = quantify(s, &vars[1..], f, env, all);
        match saved {
            Some(old) => {
                env.insert(vars[0].clone(), old);
            }
            None => {
                env.remove(&vars[0]);
            }
        }
        if r != all {
            return r;
        }
    }
    all
}

fn satisfies(s: &Shape, theory: &Theory<FOF>) -> Result<(), String> {
    for sentence in theory.formulae() {
        let free: Vec<Var> = sentence.free_vars().into_iter().cloned().collect();
        if !quantify(s, &free, sentence, &mut HashMap::new(), true) {
            return Err(format!("{} fails", sentence));
        }
    }
    Ok(())
}

fn check_all<M: Model<TermType = BasicWitnessTerm> + std::fmt::Debug>(
    name: &str,
    theory: &Theory<FOF>,
    models: &[M],
) {
    for m in models {
        if let Err(why) = satisfies(&shape(m), theory) {
            panic!(
                "{}: a returned model does not satisfy the theory: {}\n{:?}",
                name, why, m
            );
        }
    }
}

#[test]
fn models_satisfy_the_theory_on_core_fixtures() {
    for (name, theory) in core_theories() {
        let (complete, incomplete) = run_db(&theory, &Unbounded);
        assert!(incomplete.is_empty());
        check_all(&format!("{} restricted", name), &theory, &complete);
        check_all(&format!("{} basic", name), &theory, &run_basic(&theory));
    }
}

#[test]
fn models_satisfy_the_theory_on_examples() {
    for (file, bound) in [
        ("toy", &Unbounded as &dyn Bounder),
        ("valar-morghulis", &Unbounded as &dyn Bounder),
        ("golden-lion", &Unbounded as &dyn Bounder),
        ("lannisters", &Unbounded as &dyn Bounder),
        ("grandpa", &Unbounded as &dyn Bounder),
        (
            "grandpa",
            &Depth {
                max: 2,
                mode: DepthMode::Reuse,
            },
        ),
        (
            "hodor-time-loop",
            &Depth {
                max: 3,
                mode: DepthMode::Reuse,
            },
        ),
        (
            "hodor-linear",
            &Depth {
                max: 3,
                mode: DepthMode::Reuse,
            },
        ),
    ] {
        let theory = read_theory_from_file(&format!("../theories/examples/{}.raz", file));
        let (complete, _) = run_db(&theory, bound);
        check_all(&format!("{} {:?}", file, bound), &theory, &complete);
    }
}

#[test]
fn model_checker_rejects_wrong_models() {
    let theory: Theory<FOF> = "P('a); P(x) -> Q(x); exists y. R('a, y);".parse().unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    let mut s = shape(&complete[0]);
    assert!(satisfies(&s, &theory).is_ok());
    s.facts.remove(&("Q".to_string(), vec![0]));
    assert!(
        satisfies(&s, &theory).is_err(),
        "a missing Q fact must be detected"
    );
    let mut s = shape(&complete[0]);
    s.facts.retain(|(r, _)| r != "R");
    assert!(
        satisfies(&s, &theory).is_err(),
        "a missing witness must be detected"
    );
}

#[test]
fn restricted_chase_reuses_a_witness_created_in_the_same_step() {
    let theory: Theory<FOF> = "P('a); P('b); P(x) -> exists z. Q(z);".parse().unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    check_all("one witness", &theory, &complete);
    let s = shape(&complete[0]);
    assert_eq!(3, s.size);
    assert_eq!(1, s.count("Q"));
}

#[test]
fn merging_a_constant_into_a_deeper_element_keeps_the_smaller_depth() {
    // The witness y (depth 1) is created before 'b (depth 0) and wins the merge; it must take
    // depth 0, or the witness of z (depth 2) exceeds the bound.
    let theory: Theory<FOF> = "P('a); P(x) -> exists y. Q(x, y); Q(x, y) -> (y = 'b & R('b)); \
         R(y) & Q(x, y) -> exists z. T(y, z);"
        .parse()
        .unwrap();
    let (complete, incomplete) = run_db(
        &theory,
        &Depth {
            max: 1,
            mode: DepthMode::Pure,
        },
    );
    assert!(incomplete.is_empty());
    assert_eq!(1, complete.len());
    check_all("depth after merge", &theory, &complete);
    assert_eq!(3, complete[0].size());
}

#[test]
fn a_user_variable_named_like_a_placeholder_stays_universal() {
    let x = || Complex::from(Var::from("?x"));
    let body = FOF::from(Pred::from("P").app(vec![x()]));
    let head = FOF::from(Pred::from("Q").app(vec![x()]));
    let fact = FOF::from(Pred::from("P").app(vec![Complex::from(Const::from("a"))]));
    let theory: Theory<FOF> = [fact, body.implies(head)].into_iter().collect();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    let s = shape(&complete[0]);
    assert_eq!((1, 1), (s.size, s.count("Q")));
}

#[test]
fn a_user_predicate_named_like_a_constant_relation_is_a_predicate() {
    let fact = Pred::from("@p").app(vec![Complex::from(Const::from("a"))]);
    let theory: Theory<FOF> = std::iter::once(FOF::from(fact)).collect();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    assert_eq!(1, shape(&complete[0]).count("@p"));
}

#[test]
fn split_conjunctive_head_shares_one_witness() {
    // Neither 'b nor 'c is both Q and R, so one y is created carrying both.
    let theory: Theory<FOF> = "P('a); Q('b); R('c); P(x) -> exists y. (Q(y) & R(y));"
        .parse()
        .unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    check_all("split head", &theory, &complete);
    assert_eq!(4, complete[0].size(), "{:?}", complete[0]);
}

#[test]
fn split_conjunctive_head_is_witnessed_as_a_whole() {
    // 'b witnesses the merged head, so no element is created.
    let theory: Theory<FOF> = "P('a); Q('b); R('b); P(x) -> exists y. (Q(y) & R(y));"
        .parse()
        .unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    check_all("witnessed split head", &theory, &complete);
    assert_eq!(2, complete[0].size(), "{:?}", complete[0]);
}

#[test]
fn same_step_witness_reuse_survives_a_head_function() {
    let theory: Theory<FOF> = "P('a); P('b); P(x) -> exists y. (Q(y) & f(y) = 'c);"
        .parse()
        .unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    check_all("reuse with a head function", &theory, &complete);
    let s = shape(&complete[0]);
    assert_eq!(4, s.size, "{:?}", complete[0]);
    assert_eq!(1, s.count("Q"), "{:?}", complete[0]);
}

/// `f(f(...f(x)))` with `depth` applications.
fn nested(depth: usize, x: &str) -> String {
    (0..depth).fold(x.to_string(), |term, _| format!("f({})", term))
}

#[test]
fn a_nested_term_used_twice_is_one_application() {
    for depth in 1..=4 {
        let term = nested(depth, "x");
        let in_body = format!(
            "P('a); {} = 'b; {term} = y & {term} = z -> Q(y, z);",
            nested(depth, "'a")
        );
        let in_head = format!("P('a); P(x) -> exists y. ({term} = y & Q({term}));");
        for theory in [in_body, in_head] {
            let theory: Theory<FOF> = theory.parse().unwrap();
            let (complete, _) = run_db(&theory, &Unbounded);
            assert_eq!(1, complete.len());
            check_all(&format!("depth {depth}"), &theory, &complete);
            let s = shape(&complete[0]);
            assert_eq!(1, s.count("Q"), "depth {depth}: {:?}", complete[0]);
        }
    }
}

#[test]
fn chase_step_bounds_the_relational_chase() {
    let theory: Theory<FOF> = "exists x. P(x); P(x) -> exists y. (R(x, y) & P(y));"
        .parse()
        .unwrap();
    let (sequents, init) = RelPreProcessor.pre_process(&theory);
    let strategy: Bootstrap<_, Fair<_>> = sequents.iter().collect();
    let mut scheduler = FIFO::new();
    scheduler.add(init, strategy);
    let bound = DomainSize(3);
    let mut incomplete = Vec::new();
    // without the bound the chase never stops, so the steps are capped:
    for _ in 0..100 {
        if scheduler.empty() {
            break;
        }
        chase_step(
            &mut scheduler,
            &RelEvaluator,
            &bound,
            |_| {},
            |m| incomplete.push(m),
        );
    }
    assert!(scheduler.empty());
    assert_eq!(1, incomplete.len());
}

#[test]
fn unrelated_heads_of_one_body_stay_apart() {
    // 'b witnesses the first formula, so only the second creates an element.
    let theory: Theory<FOF> = "P('a); Q('b); P(x) -> exists y. Q(y); P(x) -> exists z. R(z);"
        .parse()
        .unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    assert_eq!(1, complete.len());
    check_all("unrelated heads", &theory, &complete);
    assert_eq!(3, complete[0].size(), "{:?}", complete[0]);
}

#[test]
fn an_existential_over_a_universal_is_one_element() {
    let theory: Theory<FOF> = "Q('b, 'd); exists y. forall u. Q(u, y);".parse().unwrap();
    let (complete, incomplete) = run_db(&theory, &Unbounded);
    assert!(incomplete.is_empty());
    assert_eq!(1, complete.len());
    check_all("∃y ∀u", &theory, &complete);
    let s = shape(&complete[0]);
    let index = |c: &str| s.constants.iter().find(|(n, _)| n == c).unwrap().1;
    let (b, d) = (index("b"), index("d"));
    assert!(
        (0..s.size).any(|y| {
            s.facts.contains(&("Q".to_string(), vec![b, y]))
                && s.facts.contains(&("Q".to_string(), vec![d, y]))
        }),
        "{:?}",
        complete[0]
    );

    let theory: Theory<FOF> = "Q('a, 'b); forall x. (Q('b, x) -> exists v1. forall v2. v2 = v1);"
        .parse()
        .unwrap();
    let (complete, _) = run_db(&theory, &Unbounded);
    check_all("∃v1 ∀v2", &theory, &complete);
}

// ---------------------------------------------------------------------------------------------
// Sets of support: two chases that fire sequents in different orders may return different
// models, but each returned set must map homomorphically into every model of the theory, in
// particular into every model the other chase returns.

impl Shape {
    /// The reduct to `theory`'s own signature: the symbols Skolemization introduced are an
    /// artifact of one chase and not part of the language models are compared in.
    fn reduct(&self, theory: &Theory<FOF>) -> Shape {
        let sig = theory.signature().expect("invalid signature");
        Shape {
            size: self.size,
            facts: self.facts.clone(),
            functions: self
                .functions
                .iter()
                .filter(|(f, _, _)| sig.functions().contains_key(f))
                .cloned()
                .collect(),
            constants: self
                .constants
                .iter()
                .filter(|(c, _)| sig.constants().contains(&Const::from(c.as_str())))
                .cloned()
                .collect(),
        }
    }

    /// Facts, function entries (output last) and constants as one set of tagged tuples.
    fn tuples(&self) -> BTreeSet<(String, Vec<usize>)> {
        let functions = self.functions.iter().map(|(f, args, out)| {
            let mut tuple = args.clone();
            tuple.push(*out);
            (format!("${}", f), tuple)
        });
        let constants = self
            .constants
            .iter()
            .map(|(c, e)| (format!("@{}", c), vec![*e]));
        self.facts
            .iter()
            .cloned()
            .chain(functions)
            .chain(constants)
            .collect()
    }
}

/// Is there a map from the elements of `from` to those of `to` preserving every fact, function
/// entry and constant?
fn homomorphic(from: &Shape, to: &Shape) -> bool {
    let source = from.tuples();
    let target = to.tuples();
    // Every (symbol, position) an element occupies, which its image must occupy too:
    let roles = |tuples: &BTreeSet<(String, Vec<usize>)>, e: usize| -> BTreeSet<(String, usize)> {
        tuples
            .iter()
            .flat_map(|(r, ts)| {
                ts.iter()
                    .enumerate()
                    .filter(move |(_, t)| **t == e)
                    .map(move |(i, _)| (r.clone(), i))
            })
            .collect()
    };
    let candidates: Vec<Vec<usize>> = (0..from.size)
        .map(|e| {
            let needed = roles(&source, e);
            (0..to.size)
                .filter(|c| needed.is_subset(&roles(&target, *c)))
                .collect()
        })
        .collect();
    // A tuple is checked once its largest element is assigned:
    let mut checks: Vec<Vec<&(String, Vec<usize>)>> = vec![Vec::new(); from.size];
    for tuple in &source {
        if let Some(last) = tuple.1.iter().max() {
            checks[*last].push(tuple);
        }
    }
    fn go(
        e: usize,
        map: &mut Vec<usize>,
        candidates: &[Vec<usize>],
        checks: &[Vec<&(String, Vec<usize>)>],
        target: &BTreeSet<(String, Vec<usize>)>,
    ) -> bool {
        if e == candidates.len() {
            return true;
        }
        for &c in &candidates[e] {
            map[e] = c;
            let preserved = checks[e]
                .iter()
                .all(|(r, ts)| target.contains(&(r.clone(), ts.iter().map(|t| map[*t]).collect())));
            if preserved && go(e + 1, map, candidates, checks, target) {
                return true;
            }
        }
        false
    }
    go(0, &mut vec![0; from.size], &candidates, &checks, &target)
}

/// Does every model in `others` receive a homomorphism from some model in `models`?
fn set_of_support(models: &[Shape], others: &[Shape]) -> bool {
    others
        .iter()
        .all(|other| models.iter().any(|m| homomorphic(m, other)))
}

/// The reducts of `models` to `theory`'s signature.
fn reducts<M: Model<TermType = BasicWitnessTerm>>(
    theory: &Theory<FOF>,
    models: &[M],
) -> Vec<Shape> {
    models.iter().map(|m| shape(m).reduct(theory)).collect()
}

/// A shape over `size` elements with the given facts.
fn fact_shape(size: usize, facts: &[(&str, &[usize])]) -> Shape {
    Shape {
        size,
        facts: facts
            .iter()
            .map(|(r, ts)| (r.to_string(), ts.to_vec()))
            .collect(),
        functions: BTreeSet::new(),
        constants: BTreeSet::new(),
    }
}

#[test]
fn homomorphism_checker_distinguishes_shapes() {
    // a P-loop absorbs a P-path, but not the other way around:
    let path = fact_shape(3, &[("P", &[0, 1]), ("P", &[1, 2])]);
    let mut lasso = fact_shape(1, &[("P", &[0, 0])]);
    assert!(homomorphic(&path, &lasso));
    assert!(!homomorphic(&lasso, &path));
    // a fact the target lacks:
    let more = fact_shape(1, &[("P", &[0, 0]), ("Q", &[0])]);
    assert!(homomorphic(&lasso, &more));
    assert!(!homomorphic(&more, &lasso));
    // the constant pins the image, and the function entry must map to an entry:
    lasso.constants.insert(("a".to_string(), 0));
    lasso.functions.insert(("f".to_string(), vec![0], 0));
    let mut split = fact_shape(2, &[("P", &[0, 0]), ("P", &[1, 1])]);
    split.constants.insert(("a".to_string(), 0));
    split.functions.insert(("f".to_string(), vec![0], 1));
    assert!(!homomorphic(&lasso, &split));
    assert!(homomorphic(&split, &lasso));
    split.functions = BTreeSet::from([("f".to_string(), vec![1], 1)]);
    assert!(!homomorphic(&lasso, &split), "f(a) has no image");
    assert!(homomorphic(&lasso, &lasso));
}

#[test]
fn restricted_chase_and_basic_support_each_other_on_core_fixtures() {
    for (name, theory) in core_theories() {
        let basic = run_basic(&theory);
        let (restricted, _) = run_db(&theory, &Unbounded);
        check_all(&format!("{} basic", name), &theory, &basic);
        check_all(&format!("{} restricted", name), &theory, &restricted);
        let (basic, restricted) = (reducts(&theory, &basic), reducts(&theory, &restricted));
        assert!(
            set_of_support(&basic, &restricted),
            "{}: basic does not support the restricted models\nbasic: {:#?}\nrestricted: {:#?}",
            name,
            basic,
            restricted
        );
        assert!(
            set_of_support(&restricted, &basic),
            "{}: the restricted models do not support basic\nbasic: {:#?}\nrestricted: {:#?}",
            name,
            basic,
            restricted
        );
    }
}

/// The pairs `(a, b)` of `models` where `a` maps into `b` but not back, so `b` is not minimal.
fn non_minimal(models: &[Shape]) -> Vec<(usize, usize)> {
    let mut pairs = Vec::new();
    for (i, a) in models.iter().enumerate() {
        for (j, b) in models.iter().enumerate() {
            if i != j && homomorphic(a, b) && !homomorphic(b, a) {
                pairs.push((i, j));
            }
        }
    }
    pairs
}

#[test]
fn restricted_models_are_homomorphically_minimal_on_core_fixtures() {
    for (name, theory) in core_theories() {
        let (restricted, _) = run_db(&theory, &Unbounded);
        let models = reducts(&theory, &restricted);
        let pairs = non_minimal(&models);
        assert!(
            pairs.is_empty(),
            "{}: model b receives a strict homomorphism from model a in {:?}\n{:#?}",
            name,
            pairs,
            models
        );
    }
}

// ---------------------------------------------------------------------------------------------
// Differential testing on random geometric and first-order theories: within a domain bound,
// the restricted chase and the basic implementation must return models of the theory that
// support each other. Only a run the bound did not cut is a set of support for all models.

/// A seeded xorshift64* source of choices, so a theory is reproducible from its seed.
struct Dice(u64);

impl Dice {
    fn new(seed: u64) -> Self {
        Dice(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    /// A number in `0..n`.
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        (self.0.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 33) as usize % n
    }

    /// True with probability `1/n`.
    fn one_in(&mut self, n: usize) -> bool {
        self.below(n) == 0
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len())]
    }
}

/// The first-order shapes a draw may produce beyond geometric sequents. The default produces
/// none of them, so a draw under it is a geometric theory.
#[derive(Clone, Copy, Default)]
struct Shapes {
    /// A nested existential conjunct in a head: `exists z. (P(z) & exists w. Q(z, w))`.
    nested_existentials: bool,
    /// A universal conjunct in a head, also under an existential:
    /// `exists z. (P(z) & forall u. (Q(u, z) | R(u)))`.
    head_universals: bool,
    /// An implication conjunct in a head, so an existential occurs negatively in its scope:
    /// `exists z. (P(z) & (Q(z) -> R(z)))`.
    head_implications: bool,
    /// A formula with no body, so an existential may stand at its top: `exists z. P(z)`.
    bodiless: bool,
}

impl Shapes {
    /// Every shape on.
    fn first_order() -> Self {
        Self {
            nested_existentials: true,
            head_universals: true,
            head_implications: true,
            bodiless: true,
        }
    }
}

/// The variable an existential binds at each nesting depth, so no binder shadows another.
const EXISTENTIALS: [&str; 2] = ["z", "w"];
/// The variable a universal in a head binds.
const UNIVERSAL: &str = "u";

/// Draws a theory over predicates `P`, `Q`, `R` (each of arity 1 or 2, fixed per theory), the
/// function `f/1`, the constants `'a`, `'b`, the variables `x`, `y` (universal in a body), and
/// in heads the variables of `EXISTENTIALS` and `UNIVERSAL`, nested at most one deep. `shapes`
/// adds first-order shapes to the geometric sequents.
struct TheoryDraw {
    dice: Dice,
    arity: [usize; 3],
    shapes: Shapes,
}

impl TheoryDraw {
    fn new(seed: u64, shapes: Shapes) -> Self {
        let mut dice = Dice::new(seed);
        let arity = [1 + dice.below(2), 1 + dice.below(2), 1 + dice.below(2)];
        Self {
            dice,
            arity,
            shapes,
        }
    }

    /// A leaf of `leaves`, under `f` one time in four; the variables used go into `used`.
    fn term(&mut self, leaves: &[&'static str], used: &mut BTreeSet<&'static str>) -> String {
        let leaf = *self.dice.pick(leaves);
        if !leaf.starts_with('\'') {
            used.insert(leaf);
        }
        if self.dice.one_in(4) {
            format!("f({})", leaf)
        } else {
            leaf.to_string()
        }
    }

    /// An equation one time in four, otherwise a predicate atom.
    fn atom(&mut self, leaves: &[&'static str], used: &mut BTreeSet<&'static str>) -> String {
        if self.dice.one_in(4) {
            let left = self.term(leaves, used);
            let right = self.term(leaves, used);
            return format!("{} = {}", left, right);
        }
        let p = self.dice.below(3);
        let terms: Vec<String> = (0..self.arity[p])
            .map(|_| self.term(leaves, used))
            .collect();
        format!("{}({})", ["P", "Q", "R"][p], terms.join(", "))
    }

    /// A conjunction of `1..=max` atoms.
    fn conjunction(
        &mut self,
        max: usize,
        leaves: &[&'static str],
        used: &mut BTreeSet<&'static str>,
    ) -> String {
        let n = 1 + self.dice.below(max);
        let atoms: Vec<String> = (0..n).map(|_| self.atom(leaves, used)).collect();
        atoms.join(" & ")
    }

    /// A conjunction over `vars` and the constants.
    fn disjunct(&mut self, vars: &[&'static str], used: &mut BTreeSet<&'static str>) -> String {
        let mut leaves = vars.to_vec();
        leaves.extend(["'a", "'b"]);
        self.existential(&leaves, 0, used)
    }

    /// A conjunction over `leaves`, existentially quantified over the existential of `depth`
    /// half the time it occurs, with the conjuncts of `shapes` at the outer depth.
    fn existential(
        &mut self,
        leaves: &[&'static str],
        depth: usize,
        used: &mut BTreeSet<&'static str>,
    ) -> String {
        let z = EXISTENTIALS[depth];
        let mut leaves = leaves.to_vec();
        if self.dice.one_in(2) {
            leaves.extend([z, z]);
        }
        let mut inner = BTreeSet::new();
        let mut conjuncts = vec![self.conjunction(2 - depth, &leaves, &mut inner)];
        if depth == 0 {
            conjuncts.extend(self.nested(&leaves, &mut inner));
        }
        let conjunction = conjuncts.join(" & ");
        let bound = inner.remove(z);
        used.extend(inner);
        if bound {
            format!("(exists {}. ({}))", z, conjunction)
        } else {
            format!("({})", conjunction)
        }
    }

    /// The conjuncts `shapes` nests in a head over `leaves`, each drawn independently.
    fn nested(
        &mut self,
        leaves: &[&'static str],
        used: &mut BTreeSet<&'static str>,
    ) -> Vec<String> {
        let mut conjuncts = Vec::new();
        if self.shapes.nested_existentials && self.dice.one_in(4) {
            conjuncts.push(self.existential(leaves, 1, used));
        }
        if self.shapes.head_universals && self.dice.one_in(6) {
            conjuncts.push(self.universal(leaves, used));
        }
        if self.shapes.head_implications && self.dice.one_in(4) {
            let premise = self.atom(leaves, used);
            let consequence = self.atom(leaves, used);
            conjuncts.push(format!("({} -> {})", premise, consequence));
        }
        conjuncts
    }

    /// A disjunction of one or two existentials over `leaves` and a universal, quantified when
    /// it occurs.
    fn universal(&mut self, leaves: &[&'static str], used: &mut BTreeSet<&'static str>) -> String {
        let u = UNIVERSAL;
        let mut leaves = leaves.to_vec();
        leaves.extend([u, u]);
        let mut inner = BTreeSet::new();
        let disjuncts: Vec<String> = (0..1 + self.dice.one_in(3) as usize)
            .map(|_| self.existential(&leaves, 1, &mut inner))
            .collect();
        let disjunction = disjuncts.join(" | ");
        let bound = inner.remove(u);
        used.extend(inner);
        if bound {
            format!("(forall {}. ({}))", u, disjunction)
        } else {
            format!("({})", disjunction)
        }
    }

    /// One or two disjuncts over `vars`; the free variables used go into `used`.
    fn head(&mut self, vars: &[&'static str], used: &mut BTreeSet<&'static str>) -> String {
        let head: Vec<String> = (0..1 + self.dice.below(2))
            .map(|_| self.disjunct(vars, used))
            .collect();
        head.join(" | ")
    }

    /// `sentence` universally quantified over `vars`.
    fn close(vars: &[&'static str], sentence: String) -> String {
        if vars.is_empty() {
            sentence
        } else {
            format!("forall {}. ({})", vars.join(", "), sentence)
        }
    }

    /// A sequent, or one time in four under `shapes.bodiless`, a head on its own.
    fn sentence(&mut self) -> String {
        if self.shapes.bodiless && self.dice.one_in(4) {
            let vars: &[&'static str] = if self.dice.one_in(2) { &["x"] } else { &[] };
            let mut used = BTreeSet::new();
            let head = self.head(vars, &mut used);
            let used: Vec<&'static str> = used.into_iter().collect();
            return Self::close(&used, head);
        }
        let mut vars = BTreeSet::new();
        let body = match self.dice.below(3) {
            0 => "true".to_string(),
            n => (0..n)
                .map(|_| self.atom(&["x", "y", "'a", "'b"], &mut vars))
                .collect::<Vec<_>>()
                .join(" & "),
        };
        let vars: Vec<&'static str> = vars.into_iter().collect();
        let head = self.head(&vars, &mut BTreeSet::new());
        Self::close(&vars, format!("{} -> {}", body, head))
    }

    fn theory(mut self) -> String {
        let n = 2 + self.dice.below(4);
        (0..n).map(|_| self.sentence() + ";\n").collect()
    }
}

/// The text of the random geometric theory of `seed`.
fn random_theory(seed: u64) -> String {
    TheoryDraw::new(seed, Shapes::default()).theory()
}

/// The text of the random first-order theory of `seed`, with every shape of `Shapes`.
fn random_first_order_theory(seed: u64) -> String {
    TheoryDraw::new(seed, Shapes::first_order()).theory()
}

#[test]
fn random_theory_is_reproducible() {
    assert_eq!(random_theory(7), random_theory(7));
    assert_eq!(
        "forall y. (P(y) -> (R(f('a))) | (P('b) & y = 'b));\n\
         Q('a) -> (P('b)) | (P('b));\n",
        random_theory(7)
    );
}

/// The complete models of one engine on a theory, reduced to the theory's signature.
struct Outcome {
    engine: &'static str,
    models: Vec<Shape>,
    /// Did the bound cut a branch? Then `models` need not support every model.
    cut: bool,
}

impl Outcome {
    /// Checks that every complete model satisfies `theory`.
    fn new<M: Model<TermType = BasicWitnessTerm>>(
        engine: &'static str,
        theory: &Theory<FOF>,
        (complete, incomplete): (Vec<M>, Vec<M>),
    ) -> Result<Self, String> {
        let shapes: Vec<Shape> = complete.iter().map(shape).collect();
        for s in &shapes {
            satisfies(s, theory)
                .map_err(|why| format!("{}: unsatisfying model: {}\n{:?}", engine, why, s))?;
        }
        Ok(Self {
            engine,
            models: shapes.iter().map(|s| s.reduct(theory)).collect(),
            cut: !incomplete.is_empty(),
        })
    }

    /// Fails when this run was not cut and misses a model below one of `other`.
    fn supports(&self, other: &Outcome) -> Result<(), String> {
        if self.cut || set_of_support(&self.models, &other.models) {
            Ok(())
        } else {
            Err(format!(
                "{} does not support {}\n{}: {:#?}\n{}: {:#?}",
                self.engine, other.engine, self.engine, self.models, other.engine, other.models
            ))
        }
    }
}

// ---------------------------------------------------------------------------------------------
// A brute-force oracle: the structures with one or two elements over a theory's signature,
// with total functions as in first-order logic. A theory with such a model is satisfiable, so a
// run the bound did not cut must return a model of it.

/// The most structures `tiny_model_exists` enumerates for one theory.
const TINY_BUDGET: usize = 100_000;

/// A symbol entry a structure decides: a tuple of a predicate (in or out), the output of a
/// function on a tuple, or the element of a constant.
enum Slot {
    Fact(String, Vec<usize>),
    Entry(String, Vec<usize>),
    Constant(String),
}

impl Slot {
    /// The number of ways to decide `self` over `size` elements.
    fn radix(&self, size: usize) -> usize {
        match self {
            Slot::Fact(..) => 2,
            Slot::Entry(..) | Slot::Constant(_) => size,
        }
    }
}

/// The tuples of `arity` elements of a domain of `size`.
fn tuples(size: usize, arity: usize) -> Vec<Vec<usize>> {
    (0..arity).fold(vec![Vec::new()], |tuples, _| {
        tuples
            .into_iter()
            .flat_map(|t| {
                (0..size).map(move |e| {
                    let mut t = t.clone();
                    t.push(e);
                    t
                })
            })
            .collect()
    })
}

/// The structures over `size` elements for a signature, enumerated as the digits of a
/// mixed-radix counter with one digit per [`Slot`].
struct Structures {
    size: usize,
    slots: Vec<Slot>,
    digits: Option<Vec<usize>>,
}

impl Structures {
    fn new(size: usize, theory: &Theory<FOF>) -> Self {
        let sig = theory.signature().expect("invalid signature");
        let facts = sig
            .predicates()
            .values()
            .filter(|p| p.symbol.name() != EQ_SYM)
            .flat_map(|p| {
                let name = p.symbol.name().to_string();
                tuples(size, p.arity as usize)
                    .into_iter()
                    .map(move |t| Slot::Fact(name.clone(), t))
            });
        let entries = sig.functions().values().flat_map(|f| {
            let name = f.symbol.name().to_string();
            tuples(size, f.arity as usize)
                .into_iter()
                .map(move |t| Slot::Entry(name.clone(), t))
        });
        let constants = sig
            .constants()
            .iter()
            .map(|c| Slot::Constant(c.name().to_string()));
        let slots: Vec<Slot> = facts.chain(entries).chain(constants).collect();
        let digits = Some(vec![0; slots.len()]);
        Self {
            size,
            slots,
            digits,
        }
    }

    /// The number of structures, if it is at most `budget`.
    fn count(&self, budget: usize) -> Option<usize> {
        self.slots.iter().try_fold(1usize, |count, slot| {
            count
                .checked_mul(slot.radix(self.size))
                .filter(|c| *c <= budget)
        })
    }

    fn shape(&self, digits: &[usize]) -> Shape {
        let mut shape = fact_shape(self.size, &[]);
        for (slot, digit) in self.slots.iter().zip(digits) {
            match slot {
                Slot::Fact(p, t) if *digit == 1 => {
                    shape.facts.insert((p.clone(), t.clone()));
                }
                Slot::Fact(..) => {}
                Slot::Entry(f, t) => {
                    shape.functions.insert((f.clone(), t.clone(), *digit));
                }
                Slot::Constant(c) => {
                    shape.constants.insert((c.clone(), *digit));
                }
            }
        }
        shape
    }
}

impl Iterator for Structures {
    type Item = Shape;

    fn next(&mut self) -> Option<Shape> {
        let digits = self.digits.take()?;
        let shape = self.shape(&digits);
        let mut next = digits;
        let carried = next.iter_mut().zip(&self.slots).all(|(digit, slot)| {
            *digit += 1;
            if *digit == slot.radix(self.size) {
                *digit = 0;
                true
            } else {
                false
            }
        });
        if !carried {
            self.digits = Some(next);
        }
        Some(shape)
    }
}

/// Does `theory` have a model with one or two elements? `None` when there are more than
/// [`TINY_BUDGET`] structures to try.
fn tiny_model_exists(theory: &Theory<FOF>) -> Option<bool> {
    let sizes = [Structures::new(1, theory), Structures::new(2, theory)];
    sizes
        .iter()
        .try_fold(0, |total, s| s.count(TINY_BUDGET).map(|c| total + c))
        .filter(|total| *total <= TINY_BUDGET)?;
    Some(
        sizes
            .into_iter()
            .flatten()
            .any(|s| satisfies(&s, theory).is_ok()),
    )
}

#[test]
fn tiny_models_are_found_and_missed() {
    let theory = |text: &str| text.parse::<Theory<FOF>>().unwrap();
    assert_eq!(
        Some(true),
        tiny_model_exists(&theory("P('a); P(x) -> Q(f(x));"))
    );
    assert_eq!(
        Some(true),
        tiny_model_exists(&theory("~('a = 'b); P('a); ~P('b);"))
    );
    assert_eq!(
        Some(false),
        tiny_model_exists(&theory("~('a = 'b); ~('b = 'c); ~('a = 'c);"))
    );
    assert_eq!(Some(false), tiny_model_exists(&theory("P('a); ~P('a);")));
    assert_eq!(
        None,
        tiny_model_exists(&theory("R(x, y) & S(x, y) & T(x, y) & U(x, y) & V(x, y);"))
    );
}

/// What the brute-force oracle said about a theory in a differential run.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Tiny {
    /// Some engine returned a model, or was cut, so the oracle was not asked.
    Unasked,
    /// No structure with one or two elements is a model.
    Checked,
    /// The signature has more than [`TINY_BUDGET`] tiny structures.
    OverBudget,
}

/// The verdict of a differential run that found no disagreement.
struct Verdict {
    /// Was neither run cut by the bound?
    uncut: bool,
    tiny: Tiny,
}

/// Checks that the restricted chase and basic agree on `text` within `bound`, and that an
/// engine that returned no model without being cut is right that `text` has no model with
/// one or two elements.
fn differential(text: &str, bound: DomainSize) -> Result<Verdict, String> {
    let theory: Theory<FOF> = text.parse().map_err(|e| format!("parse: {:?}", e))?;
    let basic = Outcome::new("basic", &theory, run_basic_bounded(&theory, &bound))?;
    let restricted = Outcome::new("restricted", &theory, run_db(&theory, &bound))?;
    basic.supports(&restricted)?;
    restricted.supports(&basic)?;
    let empty: Vec<&str> = [&basic, &restricted]
        .iter()
        .filter(|o| !o.cut && o.models.is_empty())
        .map(|o| o.engine)
        .collect();
    let tiny = if empty.is_empty() {
        Tiny::Unasked
    } else {
        match tiny_model_exists(&theory) {
            Some(true) => {
                return Err(format!(
                    "{} returned no model, but one with at most two elements exists",
                    empty.join(" and ")
                ))
            }
            Some(false) => Tiny::Checked,
            None => Tiny::OverBudget,
        }
    };
    Ok(Verdict {
        uncut: !(basic.cut || restricted.cut),
        tiny,
    })
}

/// Runs `run` on a thread, reporting a panic or a run longer than `limit`.
fn guarded<T: Send + 'static>(
    limit: std::time::Duration,
    run: impl FnOnce() -> T + Send + 'static,
) -> Result<T, String> {
    let (send, receive) = std::sync::mpsc::channel();
    std::thread::spawn(move || send.send(run()));
    receive.recv_timeout(limit).map_err(|e| match e {
        std::sync::mpsc::RecvTimeoutError::Timeout => "timeout".to_string(),
        std::sync::mpsc::RecvTimeoutError::Disconnected => "panic".to_string(),
    })
}

/// Runs `differential` within `bound` on the theories `draw` gives seeds `0..seeds`, failing
/// on any disagreement, panic or timeout.
fn agree_with_basic(draw: fn(u64) -> String, seeds: u64, bound: DomainSize) {
    let mut failures = Vec::new();
    let mut verdicts = Vec::new();
    for seed in 0..seeds {
        let text = draw(seed);
        let theory = text.clone();
        let verdict = guarded(std::time::Duration::from_secs(10), move || {
            differential(&theory, bound)
        });
        match verdict.and_then(|v| v) {
            Ok(verdict) => verdicts.push(verdict),
            Err(why) => failures.push(format!("seed {}:\n{}{}", seed, text, why)),
        }
    }
    let tiny = |t: Tiny| verdicts.iter().filter(|v| v.tiny == t).count();
    println!(
        "{} of {} seeds agree, no engine was cut on {}; the tiny-model oracle confirmed {} \
         empty runs and skipped {} over budget",
        seeds - failures.len() as u64,
        seeds,
        verdicts.iter().filter(|v| v.uncut).count(),
        tiny(Tiny::Checked),
        tiny(Tiny::OverBudget)
    );
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn random_theories_agree_with_basic() {
    agree_with_basic(random_theory, 300, DomainSize(4));
}

#[test]
fn random_first_order_theory_is_reproducible() {
    assert_eq!(random_first_order_theory(7), random_first_order_theory(7));
    assert_eq!(
        "(Q('a) & (forall u. ((P(u)) | (exists w. (R(w)))))) | (exists z. (Q(f(z)) & ((z = z))));\n\
         forall x. (R('b) & R(f(x)) -> (P('b) & (exists w. (Q(w))) & (Q(f('a)) -> Q('a))) | \
         (exists z. (f(z) = z & (Q(z)) & ((exists w. (f(w) = z))))));\n",
        random_first_order_theory(7)
    );
}

/// Head universals branch once per element, so the bound is one smaller than for geometric
/// theories to keep the oracle fast.
#[test]
fn random_first_order_theories_agree_with_basic() {
    agree_with_basic(random_first_order_theory, 300, DomainSize(3));
}

// Conversion bugs found by `random_first_order_theories_agree_with_basic` (seeds 47, 132, 236
// and 7, 228, 233 of the conversion through prenex and Skolem normal form), reduced by hand.

/// Panics unless both engines return only models of `text`.
fn assert_both_satisfy(text: &str) {
    let theory: Theory<FOF> = text.parse().unwrap();
    check_all(text, &theory, &run_basic(&theory));
    let (complete, incomplete) = run_db(&theory, &Unbounded);
    assert!(incomplete.is_empty(), "{}", text);
    check_all(text, &theory, &complete);
}

/// Skolemizing `exists z. ~P(z)` puts its Skolem constant only in a body; without the claim
/// that the constant denotes an element, no sequent creates it and the model keeps `P('a)`
/// without a witness.
#[test]
fn a_skolem_term_in_a_body_names_an_element() {
    assert_both_satisfy("P('a); exists z. (P(z) -> Q(z));");
}

/// Prenexing scoped `exists z` under `forall u`, so `z` became a Skolem function of `u`, a
/// variable of the head alone; with no elements the sequent never fired and the empty model
/// was returned. Without prenexing, the witness of `z` depends on no variable.
#[test]
fn an_existential_beside_a_head_universal_fires_without_elements() {
    assert_both_satisfy("(R('a) & forall u. P(u)) | exists z. Q(z);");
}

// Engine bugs found by `random_theories_agree_with_basic`, reduced by hand.

#[test]
fn restricted_chase_witnesses_a_trivial_equation() {
    for text in ["exists z. z = z;", "exists z, w. z = w;"] {
        let theory: Theory<FOF> = text.parse().unwrap();
        let (complete, incomplete) = run_db(&theory, &Unbounded);
        assert!(incomplete.is_empty(), "{}", text);
        assert_eq!(1, complete.len(), "{}", text);
        check_all(text, &theory, &complete);
        assert_eq!(1, complete[0].size(), "{}: {:?}", text, complete[0]);
    }
}

/// Panics unless every fact of `model` is over elements of its domain.
fn assert_facts_in_domain(model: &BasicModel) {
    let domain = model.domain();
    for fact in model.facts() {
        if let Observation::Fact { terms, .. } = &fact {
            assert!(
                terms
                    .iter()
                    .all(|t| matches!(t, BasicWitnessTerm::Elem(e) if domain.contains(e))),
                "{} is outside the domain\n{:?}",
                fact,
                model
            );
        }
    }
}

#[test]
fn basic_merges_congruent_applications() {
    // 'a = 'b makes f('a) and f('b) one element, which carries both facts.
    let theory: Theory<FOF> = "P(f('b)); Q(f('a)); 'a = 'b;".parse().unwrap();
    let models = run_basic(&theory);
    assert_eq!(1, models.len());
    assert_facts_in_domain(&models[0]);
    assert_eq!(2, models[0].domain().len(), "{:?}", models[0]);
    check_all("congruent applications", &theory, &models);
}

#[test]
fn basic_terminates_within_a_domain_bound() {
    let theory: Theory<FOF> = "'a = 'b; y = y -> 'a = f('b) | Q(f(y));".parse().unwrap();
    let run = guarded(std::time::Duration::from_secs(10), move || {
        let (complete, incomplete) = run_basic_bounded(&theory, &DomainSize(3));
        complete
            .iter()
            .chain(&incomplete)
            .for_each(assert_facts_in_domain);
        check_all("bounded congruence", &theory, &complete);
    });
    assert!(run.is_ok(), "{:?}", run);
}
