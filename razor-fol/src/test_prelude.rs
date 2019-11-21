use crate::syntax::*;
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

pub fn u() -> Term { V::from("u").into() }

pub fn v() -> Term { V::from("v").into() }

pub fn w() -> Term { V::from("w").into() }

pub fn x() -> Term { V::from("x").into() }

pub fn x_1() -> Term { V::from("x`").into() }

pub fn y() -> Term { V::from("y").into() }

pub fn z() -> Term { V::from("z").into() }

// Functions
pub fn f() -> F { F::from("f") }

pub fn g() -> F { F::from("g") }

pub fn h() -> F { F::from("h") }

// Constants
pub fn _a() -> C { C::from("a") }

pub fn _b() -> C { C::from("b") }

pub fn _c() -> C { C::from("c") }

pub fn _d() -> C { C::from("d") }

pub fn a() -> Term { C::from("a").into() }

pub fn b() -> Term { C::from("b").into() }

#[allow(dead_code)]
pub fn c() -> Term { C::from("c").into() }

// Predicates
#[allow(non_snake_case)]
pub fn P() -> Pred { Pred::from("P") }

#[allow(non_snake_case)]
pub fn Q() -> Pred { Pred::from("Q") }

#[allow(non_snake_case)]
pub fn R() -> Pred { Pred::from("R") }

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

    contents.parse().unwrap()
}