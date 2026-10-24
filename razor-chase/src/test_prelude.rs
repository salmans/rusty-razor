use crate::chase::{r#impl::basic, *};
use itertools::Itertools;
use razor_fol::syntax::{Const, Func, Pred, Theory, FOF};
use std::{fmt, fs::File, io::Read};

pub fn equal_sets<T: Eq>(first: &[T], second: &[T]) -> bool {
    first.iter().all(|e| second.contains(e)) && second.iter().all(|e| first.contains(e))
}

// Functions
pub fn f() -> Func {
    Func::from("f")
}

pub fn g() -> Func {
    Func::from("g")
}

// Constants
pub fn _a() -> Const {
    Const::from("a")
}

pub fn _b() -> Const {
    Const::from("b")
}

pub fn _c() -> Const {
    Const::from("c")
}

pub fn _d() -> Const {
    Const::from("d")
}

// Elements
pub fn e_0() -> E {
    E::from(0)
}

pub fn e_1() -> E {
    E::from(1)
}

pub fn e_2() -> E {
    E::from(2)
}

pub fn e_3() -> E {
    E::from(3)
}

pub fn e_4() -> E {
    E::from(4)
}

// Predicates
#[allow(non_snake_case)]
pub fn R() -> Pred {
    Pred::from("R")
}

// Relations
#[allow(non_snake_case)]
pub fn _P_() -> Rel {
    Rel::from("P")
}

#[allow(non_snake_case)]
pub fn _Q_() -> Rel {
    Rel::from("Q")
}

#[allow(non_snake_case)]
pub fn _R_() -> Rel {
    Rel::from("R")
}

#[allow(non_snake_case)]
pub fn _S_() -> Rel {
    Rel::from("S")
}

impl fmt::Debug for basic::BasicSequent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub fn assert_eq_sets<T: Eq + fmt::Debug>(first: &[T], second: &[T]) {
    assert!(equal_sets(first, second));
}

pub fn assert_debug_string<T: fmt::Debug>(expected: &str, value: T) {
    debug_assert_eq!(expected, format!("{:?}", value));
}

pub fn read_file(filename: &str) -> String {
    let mut f = File::open(filename).expect("file not found");

    let mut content = String::new();
    f.read_to_string(&mut content)
        .expect("something went wrong reading the file");
    content
}

pub fn read_theory_from_file(filename: &str) -> Theory<FOF> {
    let content = read_file(filename);
    content.parse().unwrap()
}

pub fn print_basic_model(model: basic::BasicModel) -> String {
    let elements: Vec<String> = model
        .domain()
        .iter()
        .sorted()
        .map(|e| {
            let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
            let witnesses = witnesses.into_iter().sorted();
            format!("{} -> {}", witnesses.into_iter().sorted().join(", "), e)
        })
        .collect();
    let domain: Vec<String> = model.domain().iter().map(|e| e.to_string()).collect();
    let facts: Vec<String> = model.facts().iter().map(|e| e.to_string()).collect();
    format!(
        "Domain: {{{}}}\nFacts: {}\n{}",
        domain.into_iter().sorted().join(", "),
        facts.into_iter().sorted().join(", "),
        elements.join("\n")
    )
}
