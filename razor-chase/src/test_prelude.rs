use razor_fol::syntax::*;
use crate::chase::{*, r#impl::basic, r#impl::reference};
use crate::chase::{bounder::DomainSize, strategy::Linear, scheduler::FIFO};
use itertools::Itertools;
use std::{fmt, fs::File, io::Read};


pub fn equal_sets<T: Eq>(first: &[T], second: &[T]) -> bool {
    first.iter().all(|e| second.contains(e)) && second.iter().all(|e| first.contains(e))
}

// Variables
pub fn _u() -> V { V::from("u") }

pub fn _v() -> V { V::from("v") }

pub fn _w() -> V { V::from("w") }

pub fn _x() -> V { V::from("x") }

pub fn _x_1() -> V { V::from("x`") }

pub fn _y() -> V { V::from("y") }

pub fn _z() -> V { V::from("z") }

#[allow(dead_code)]
pub fn u() -> Term { V::from("u").into() }

#[allow(dead_code)]
pub fn v() -> Term { V::from("v").into() }

#[allow(dead_code)]
pub fn w() -> Term { V::from("w").into() }

#[allow(dead_code)]
pub fn x() -> Term { V::from("x").into() }

#[allow(dead_code)]
pub fn x_1() -> Term { V::from("x`").into() }

#[allow(dead_code)]
pub fn y() -> Term { V::from("y").into() }

#[allow(dead_code)]
pub fn z() -> Term { V::from("z").into() }

// Functions
pub fn f() -> F { F::from("f") }

pub fn g() -> F { F::from("g") }

#[allow(dead_code)]
pub fn h() -> F { F::from("h") }

// Constants
pub fn _a() -> C { C::from("a") }

pub fn _b() -> C { C::from("b") }

pub fn _c() -> C { C::from("c") }

pub fn _d() -> C { C::from("d") }

#[allow(dead_code)]
pub fn a() -> Term { C::from("a").into() }

#[allow(dead_code)]
pub fn b() -> Term { C::from("b").into() }

#[allow(dead_code)]
pub fn c() -> Term { C::from("c").into() }

// Elements
pub fn e_0() -> E { E::from(0) }

pub fn e_1() -> E { E::from(1) }

pub fn e_2() -> E { E::from(2) }

pub fn e_3() -> E { E::from(3) }

pub fn e_4() -> E { E::from(4) }

// Predicates
#[allow(dead_code)]
#[allow(non_snake_case)]
pub fn P() -> Pred { Pred::from("P") }

#[allow(dead_code)]
#[allow(non_snake_case)]
pub fn Q() -> Pred { Pred::from("Q") }

#[allow(non_snake_case)]
pub fn R() -> Pred { Pred::from("R") }

// Relations
#[allow(non_snake_case)]
pub fn _P_() -> Rel { Rel::from("P") }

#[allow(non_snake_case)]
pub fn _Q_() -> Rel { Rel::from("Q") }

#[allow(non_snake_case)]
pub fn _R_() -> Rel { Rel::from("R") }

#[allow(non_snake_case)]
pub fn _S_() -> Rel { Rel::from("S") }

impl fmt::Debug for basic::Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for basic::Sequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for basic::Model {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

#[allow(dead_code)]
pub fn assert_eq_vectors<T: Ord + fmt::Debug>(first: &Vec<T>, second: &Vec<T>) -> () {
    assert!(first.iter().sorted() == second.iter().sorted());
}

pub fn assert_eq_sets<T: Eq + fmt::Debug>(first: &Vec<T>, second: &Vec<T>) -> () {
    assert!(equal_sets(first, second));
}

pub fn assert_debug_string<T: fmt::Debug>(expected: &str, value: T) {
    debug_assert_eq!(expected, format!("{:?}", value));
}

#[allow(dead_code)]
pub fn assert_debug_strings<T: fmt::Debug>(expected: &str, value: Vec<T>) {
    let mut strings = value.iter().map(|v| format!("{:?}", v));
    debug_assert_eq!(expected, strings.join("\n"));
}

pub fn read_theory_from_file(filename: &str) -> Theory {
    let mut f = File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    contents.parse().unwrap()
}

pub fn solve_basic(theory: &Theory) -> Vec<basic::Model> {
    let geometric_theory = theory.gnf();
    let sequents: Vec<basic::Sequent> = geometric_theory
        .formulae
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = basic::Evaluator {};
    let strategy = Linear::new(sequents.iter().collect());
    let mut scheduler= FIFO::new();
    let bounder: Option<&DomainSize> = None;
    scheduler.add(basic::Model::new(), strategy);
    chase_all(&mut scheduler, &evaluator, bounder)
}

pub fn solve_domain_bounded_basic(theory: &Theory, bound: usize) -> Vec<basic::Model> {
    let geometric_theory = theory.gnf();
    let sequents: Vec<basic::Sequent> = geometric_theory
        .formulae
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = basic::Evaluator {};
    let strategy = Linear::new(sequents.iter().collect());
    let mut scheduler = FIFO::new();
    let bounder = DomainSize::from(bound);
    let bounder: Option<&DomainSize> = Some(&bounder);
    scheduler.add(basic::Model::new(), strategy);
    chase_all(&mut scheduler, &evaluator, bounder)
}

pub fn print_basic_model(model: basic::Model) -> String {
    let elements: Vec<String> = model.domain().iter().sorted().iter().map(|e| {
        let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
        let witnesses = witnesses.into_iter().sorted();
        format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
    }).collect();
    let domain: Vec<String> = model.domain().iter().map(|e| e.to_string()).collect();
    let facts: Vec<String> = model.facts().iter().map(|e| e.to_string()).collect();
    format!("Domain: {{{}}}\nFacts: {}\n{}",
            domain.into_iter().sorted().join(", "),
            facts.into_iter().sorted().join(", "),
            elements.join("\n"))
}

pub fn print_basic_models(models: Vec<basic::Model>) -> String {
    let models: Vec<String> = models.into_iter().map(|m| print_basic_model(m)).collect();
    models.join("\n-- -- -- -- -- -- -- -- -- --\n")
}


pub fn print_reference_model(model: reference::Model) -> String {
    let elements: Vec<String> = model.domain().iter().sorted().iter().map(|e| {
        let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
        let witnesses = witnesses.into_iter().sorted();
        format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e.get())
    }).collect();
    let domain: Vec<String> = model.domain().iter().map(|e| e.get().to_string()).collect();
    let facts: Vec<String> = model.facts().iter().map(|e| e.to_string()).collect();
    format!("Domain: {{{}}}\nFacts: {}\n{}",
            domain.into_iter().sorted().join(", "),
            facts.into_iter().sorted().join(", "),
            elements.join("\n"))
}