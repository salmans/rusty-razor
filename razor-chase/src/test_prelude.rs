use crate::chase::{bounder::DomainSize, scheduler::FIFO, strategy::Linear};
use crate::chase::{r#impl::basic, r#impl::collapse, *};
use itertools::Itertools;
use razor_fol::syntax::{term::Complex, Const, Func, Pred, Theory, Var, FOF};
use std::{fmt, fs::File, io::Read};

pub fn equal_sets<T: Eq>(first: &[T], second: &[T]) -> bool {
    first.iter().all(|e| second.contains(e)) && second.iter().all(|e| first.contains(e))
}

// Variables
pub fn _u() -> Var {
    Var::from("u")
}

pub fn _v() -> Var {
    Var::from("v")
}

pub fn _w() -> Var {
    Var::from("w")
}

pub fn _x() -> Var {
    Var::from("x")
}

pub fn _x_1() -> Var {
    Var::from("x`")
}

pub fn _y() -> Var {
    Var::from("y")
}

pub fn _z() -> Var {
    Var::from("z")
}

#[allow(dead_code)]
pub fn u() -> Complex {
    Var::from("u").into()
}

#[allow(dead_code)]
pub fn v() -> Complex {
    Var::from("v").into()
}

#[allow(dead_code)]
pub fn w() -> Complex {
    Var::from("w").into()
}

#[allow(dead_code)]
pub fn x() -> Complex {
    Var::from("x").into()
}

#[allow(dead_code)]
pub fn x_1() -> Complex {
    Var::from("x`").into()
}

#[allow(dead_code)]
pub fn y() -> Complex {
    Var::from("y").into()
}

#[allow(dead_code)]
pub fn z() -> Complex {
    Var::from("z").into()
}

// Functions
pub fn f() -> Func {
    Func::from("f")
}

pub fn g() -> Func {
    Func::from("g")
}

#[allow(dead_code)]
pub fn h() -> Func {
    Func::from("h")
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

#[allow(dead_code)]
pub fn a() -> Complex {
    Const::from("a").into()
}

#[allow(dead_code)]
pub fn b() -> Complex {
    Const::from("b").into()
}

#[allow(dead_code)]
pub fn c() -> Complex {
    Const::from("c").into()
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
#[allow(dead_code)]
#[allow(non_snake_case)]
pub fn P() -> Pred {
    Pred::from("P")
}

#[allow(dead_code)]
#[allow(non_snake_case)]
pub fn Q() -> Pred {
    Pred::from("Q")
}

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

pub fn read_theory_from_file(filename: &str) -> Theory<FOF> {
    let mut f = File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    contents.parse().unwrap()
}

pub fn solve_basic(theory: &Theory<FOF>) -> Vec<basic::BasicModel> {
    let pre_processor = basic::BasicPreProcessor;
    let (sequents, init_model) = pre_processor.pre_process(theory);

    let evaluator = basic::BasicEvaluator;
    let strategy: Linear<_> = sequents.iter().collect();

    let mut scheduler = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    scheduler.add(init_model, strategy);
    chase_all(&mut scheduler, &evaluator, bounder)
}

pub fn solve_domain_bounded_basic(theory: &Theory<FOF>, bound: usize) -> Vec<basic::BasicModel> {
    let pre_processor = basic::BasicPreProcessor;
    let (sequents, init_model) = pre_processor.pre_process(theory);
    let evaluator = basic::BasicEvaluator;
    let strategy: Linear<_> = sequents.iter().collect();
    let mut scheduler = FIFO::new();
    let bounder = DomainSize::from(bound);
    let bounder: Option<&DomainSize> = Some(&bounder);
    scheduler.add(init_model, strategy);
    chase_all(&mut scheduler, &evaluator, bounder)
}

pub fn print_basic_model(model: basic::BasicModel) -> String {
    let elements: Vec<String> = model
        .domain()
        .iter()
        .sorted()
        .iter()
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

pub fn print_basic_models(models: Vec<basic::BasicModel>) -> String {
    let models: Vec<String> = models.into_iter().map(|m| print_basic_model(m)).collect();
    models.join("\n-- -- -- -- -- -- -- -- -- --\n")
}

pub fn print_collapse_model(model: collapse::ColModel) -> String {
    let elements: Vec<String> = model
        .domain()
        .iter()
        .sorted()
        .iter()
        .map(|e| {
            let witnesses: Vec<String> = model.witness(e).iter().map(|w| w.to_string()).collect();
            let witnesses = witnesses.into_iter().sorted();
            format!(
                "{} -> {}",
                witnesses.into_iter().sorted().join(", "),
                e.get()
            )
        })
        .collect();
    let domain: Vec<String> = model.domain().iter().map(|e| e.get().to_string()).collect();
    let facts: Vec<String> = model.facts().iter().map(|e| e.to_string()).collect();
    format!(
        "Domain: {{{}}}\nFacts: {}\n{}",
        domain.into_iter().sorted().join(", "),
        facts.into_iter().sorted().join(", "),
        elements.join("\n")
    )
}
