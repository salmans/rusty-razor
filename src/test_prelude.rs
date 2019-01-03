use std::fmt;
use std::collections;
use itertools::Itertools;
use crate::formula::syntax::*;

// Variables
// Variables
pub fn _x() -> V { V::new("x") }

pub fn _y() -> V { V::new("y") }

pub fn _z() -> V { V::new("z") }

pub fn x() -> Term { V::new("x").var() }

pub fn y() -> Term { V::new("y").var() }

pub fn z() -> Term { V::new("z").var() }

// Functions
pub fn f() -> Func { Func::new("f") }

pub fn g() -> Func { Func::new("g") }

pub fn h() -> Func { Func::new("h") }

// Constants
pub fn a() -> Term { C::new("a").r#const() }

pub fn b() -> Term { C::new("b").r#const() }

// Predicates
pub fn P() -> Pred { Pred::new("P") }

pub fn Q() -> Pred { Pred::new("Q") }

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

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.to_string())
    }
}

pub fn assert_eq_vectors<T: Ord + fmt::Debug>(first: &Vec<T>, second: &Vec<T>) -> () {
    println!("{:?}", first);
    println!("{:?}", second);
    assert!(first.iter().sorted() == second.iter().sorted());
}