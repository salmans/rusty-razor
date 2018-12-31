use std::fmt;
use crate::formula::syntax::*;

// Variables
pub fn x() -> Term { Term::var("x") }

pub fn y() -> Term { Term::var("y") }

pub fn z() -> Term { Term::var("z") }

// Functions
pub fn f() -> Func { Func::new("f") }

pub fn g() -> Func { Func::new("g") }

pub fn h() -> Func { Func::new("h") }

// Constants
pub fn a() -> Term { Term::r#const("a") }

pub fn b() -> Term { Term::r#const("b") }


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
