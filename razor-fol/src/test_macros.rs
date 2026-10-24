/*! Provides a number of macros for testing purposes. */

// Asserts equality between two vectors as multisets.
#[macro_export]
macro_rules! assert_eq_sorted_vecs {
    ($left:expr, $right:expr) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                let mut l = left_val.to_vec();
                let mut r = right_val.to_vec();
                l.sort();
                r.sort();
                assert_eq!(l, r)
            }
        }
    }};
    ($left:expr, $right:expr ,) => {
        $crate::assert_eq_sorted_vecs!($left, $right)
    };
}

// Asserts that the debug representation of `value` is equal to `expected`.
#[macro_export]
macro_rules! assert_debug_string {
    ($expected:expr, $value:expr) => {{
        match (&$expected, &$value) {
            (expected_val, val) => assert_eq!(*expected_val, format!("{:?}", val)),
        }
    }};
    ($expected:expr, $value:expr ,) => {
        $crate::assert_debug_string!($expected, $value)
    };
}
