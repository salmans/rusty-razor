use std::fmt;
use itertools::Itertools;
use crate::formula::syntax::*;

// Variables
pub fn _u() -> V { V::new("u") }

pub fn _v() -> V { V::new("v") }

pub fn _w() -> V { V::new("w") }

pub fn _x() -> V { V::new("x") }
pub fn _x_1() -> V { V::new("x`") }

pub fn _y() -> V { V::new("y") }

pub fn _z() -> V { V::new("z") }

pub fn u() -> Term { V::new("u").var() }

pub fn v() -> Term { V::new("v").var() }

pub fn w() -> Term { V::new("w").var() }

pub fn x() -> Term { V::new("x").var() }
pub fn x_1() -> Term { V::new("x`").var() }

pub fn y() -> Term { V::new("y").var() }

pub fn z() -> Term { V::new("z").var() }

// Functions
pub fn f() -> Func { Func::new("f") }

pub fn g() -> Func { Func::new("g") }

pub fn h() -> Func { Func::new("h") }

// Constants
pub fn _a() -> C { C::new("a") }

pub fn _b() -> C { C::new("b") }

pub fn _c() -> C { C::new("c") }

pub fn a() -> Term { C::new("a").r#const() }

pub fn b() -> Term { C::new("b").r#const() }

pub fn c() -> Term { C::new("c").r#const() }

// Predicates
//noinspection RsFunctionNaming
pub fn P() -> Pred { Pred::new("P") }

//noinspection RsFunctionNaming
pub fn Q() -> Pred { Pred::new("Q") }

//noinspection RsFunctionNaming
pub fn R() -> Pred { Pred::new("R") }


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
        write!(f, "{:?}", self.to_string())
    }
}

impl fmt::Debug for C {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_string())
    }
}

impl fmt::Debug for Func {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_string())
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
        write!(f, "{:?}", self.to_string())
    }
}

impl fmt::Debug for Pred {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_string())
    }
}

pub fn assert_eq_vectors<T: Ord + fmt::Debug>(first: &Vec<T>, second: &Vec<T>) -> () {
    println!("{:?}", first);
    println!("{:?}", second);
    assert!(first.iter().sorted() == second.iter().sorted());
}

pub fn parse_formula(string: &str) -> Formula {
    crate::formula::parser::formula(nom::types::CompleteStr(string)).ok().unwrap().1
}

pub fn assert_debug_string<T: fmt::Debug>(expected: &str, value: T) {
    debug_assert_eq!(expected, format!("{:?}", value));
}

pub fn assert_debug_strings<T: fmt::Debug>(expected: &str, value: Vec<T>) {
    let mut strings = value.iter().map(|v| format!("{:?}", v));
    debug_assert_eq!(expected, strings.join("\n"));
}