use crate::formula::{parser::parse_theory, syntax::*};
use crate::chase::{*, r#impl::basic, r#impl::reference};
use crate::chase::{bounder::DomainSize, selector::Linear, strategy::FIFO};
use itertools::Itertools;
use std::{fmt, fs::File, io::Read};


pub fn equal_sets<T: Eq>(first: &[T], second: &[T]) -> bool {
    first.iter().all(|e| second.contains(e)) && second.iter().all(|e| first.contains(e))
}

// Variables
pub fn _u() -> V { V::new("u") }

pub fn _v() -> V { V::new("v") }

pub fn _w() -> V { V::new("w") }

pub fn _x() -> V { V::new("x") }

pub fn _x_1() -> V { V::new("x`") }

pub fn _y() -> V { V::new("y") }

pub fn _z() -> V { V::new("z") }

pub fn u() -> Term { V::new("u").into() }

pub fn v() -> Term { V::new("v").into() }

pub fn w() -> Term { V::new("w").into() }

pub fn x() -> Term { V::new("x").into() }

pub fn x_1() -> Term { V::new("x`").into() }

pub fn y() -> Term { V::new("y").into() }

pub fn z() -> Term { V::new("z").into() }

// Functions
pub fn f() -> Func { Func::new("f") }

pub fn g() -> Func { Func::new("g") }

pub fn h() -> Func { Func::new("h") }

// Constants
pub fn _a() -> C { C::new("a") }

pub fn _b() -> C { C::new("b") }

pub fn _c() -> C { C::new("c") }

pub fn _d() -> C { C::new("d") }

pub fn a() -> Term { C::new("a").into() }

pub fn b() -> Term { C::new("b").into() }

#[allow(dead_code)]
pub fn c() -> Term { C::new("c").into() }

// Elements
pub fn e_0() -> E { E::new(0) }

pub fn e_1() -> E { E::new(1) }

pub fn e_2() -> E { E::new(2) }

pub fn e_3() -> E { E::new(3) }

pub fn e_4() -> E { E::new(4) }

// Predicates
#[allow(non_snake_case)]
pub fn P() -> Pred { Pred::new("P") }

#[allow(non_snake_case)]
pub fn Q() -> Pred { Pred::new("Q") }

#[allow(non_snake_case)]
pub fn R() -> Pred { Pred::new("R") }

// Relations
#[allow(non_snake_case)]
pub fn _P_() -> Rel { Rel::new("P") }

#[allow(non_snake_case)]
pub fn _Q_() -> Rel { Rel::new("Q") }

#[allow(non_snake_case)]
pub fn _R_() -> Rel { Rel::new("R") }

#[allow(non_snake_case)]
pub fn _S_() -> Rel { Rel::new("S") }

impl PartialOrd for V {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for V {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Debug for V {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for E {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Formula::Top => write!(f, "{}", "TRUE"),
            Formula::Bottom => write!(f, "{}", "FALSE"),
            Formula::Atom { predicate, terms } => {
                let ts: Vec<String> = terms.iter().map(|t| t.to_string()).collect();
                write!(f, "{}({})", predicate.to_string(), ts.join(", "))
            }
            Formula::Equals { left, right } => write!(f, "{} = {}", left, right),
            Formula::Not { formula } => {
                match **formula {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => write!(f, "~{}", formula),
                    _ => write!(f, "~({:?})", formula)
                }
            }
            Formula::And { left, right } => {
                match **left {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "{:?} & {:?}", left, right)
                            }
                            _ => {
                                write!(f, "{:?} & ({:?})", left, right)
                            }
                        }
                    }
                    _ => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "({:?}) & {:?}", left, right)
                            }
                            _ => {
                                write!(f, "({:?}) & ({:?})", left, right)
                            }
                        }
                    }
                }
            }
            Formula::Or { left, right } => {
                match **left {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "{:?} | {:?}", left, right)
                            }
                            _ => {
                                write!(f, "{:?} | ({:?})", left, right)
                            }
                        }
                    }
                    _ => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "({:?}) | {:?}", left, right)
                            }
                            _ => {
                                write!(f, "({:?}) | ({:?})", left, right)
                            }
                        }
                    }
                }
            }
            Formula::Implies { left, right } => {
                match **left {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "{:?} -> {:?}", left, right)
                            }
                            _ => {
                                write!(f, "{:?} -> ({:?})", left, right)
                            }
                        }
                    }
                    _ => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "({:?}) -> {:?}", left, right)
                            }
                            _ => {
                                write!(f, "({:?}) -> ({:?})", left, right)
                            }
                        }
                    }
                }
            }
            Formula::Iff { left, right } => {
                match **left {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "{:?} <=> {:?}", left, right)
                            }
                            _ => {
                                write!(f, "{:?} <=> ({:?})", left, right)
                            }
                        }
                    }
                    _ => {
                        match **right {
                            Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                                write!(f, "({:?}) <=> {:?}", left, right)
                            }
                            _ => {
                                write!(f, "({:?}) <=> ({:?})", left, right)
                            }
                        }
                    }
                }
            }
            Formula::Exists { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                match **formula {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        write!(f, "? {}. {:?}", vs.join(", "), formula)
                    }
                    _ => {
                        write!(f, "? {}. ({:?})", vs.join(", "), formula)
                    }
                }
            }
            Formula::Forall { variables, formula } => {
                let vs: Vec<String> = variables.iter().map(|t| t.to_string()).collect();
                match **formula {
                    Formula::Top | Formula::Bottom | Formula::Atom { .. } => {
                        write!(f, "! {}. {:?}", vs.join(", "), formula)
                    }
                    _ => {
                        write!(f, "! {}. ({:?})", vs.join(", "), formula)
                    }
                }
            }
        }
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for Pred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl fmt::Debug for Rel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

impl<T: WitnessTermTrait> fmt::Debug for Observation<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}

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

pub fn assert_eq_vectors<T: Ord + fmt::Debug>(first: &Vec<T>, second: &Vec<T>) -> () {
    assert!(first.iter().sorted() == second.iter().sorted());
}

pub fn assert_eq_sets<T: Eq + fmt::Debug>(first: &Vec<T>, second: &Vec<T>) -> () {
    assert!(equal_sets(first, second));
}

pub fn assert_debug_string<T: fmt::Debug>(expected: &str, value: T) {
    debug_assert_eq!(expected, format!("{:?}", value));
}

pub fn assert_debug_strings<T: fmt::Debug>(expected: &str, value: Vec<T>) {
    let mut strings = value.iter().map(|v| format!("{:?}", v));
    debug_assert_eq!(expected, strings.join("\n"));
}

pub fn read_theory_from_file(filename: &str) -> Theory {
    let mut f = File::open(filename).expect("file not found");

    let mut contents = String::new();
    f.read_to_string(&mut contents)
        .expect("something went wrong reading the file");

    parse_theory(contents.as_str())
}

pub fn solve_basic(theory: &Theory) -> Vec<basic::Model> {
    let geometric_theory = theory.gnf();
    let sequents: Vec<basic::Sequent> = geometric_theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = basic::Evaluator {};
    let selector = Linear::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder: Option<&DomainSize> = None;
    strategy.add(basic::Model::new(), selector);
    solve_all(&mut strategy, &evaluator, bounder)
}

pub fn solve_domain_bounded_basic(theory: &Theory, bound: usize) -> Vec<basic::Model> {
    let geometric_theory = theory.gnf();
    let sequents: Vec<basic::Sequent> = geometric_theory
        .formulas
        .iter()
        .map(|f| f.into()).collect();

    let evaluator = basic::Evaluator {};
    let selector = Linear::new(sequents.iter().collect());
    let mut strategy = FIFO::new();
    let bounder = DomainSize::new(bound);
    let bounder: Option<&DomainSize> = Some(&bounder);
    strategy.add(basic::Model::new(), selector);
    solve_all(&mut strategy, &evaluator, bounder)
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