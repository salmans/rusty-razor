#[macro_export]
macro_rules! v_1 {
    ($v:ident) => {{
        let var = format!("{}`", stringify!($v));
        $crate::syntax::V(var)
    }};
}

#[macro_export]
macro_rules! v_2 {
    ($v:ident) => {{
        let var = format!("{}``", stringify!($v));
        $crate::syntax::V(var)
    }};
}

#[macro_export]
macro_rules! v_3 {
    ($v:ident) => {{
        let var = format!("{}```", stringify!($v));
        $crate::syntax::V(var)
    }};
}

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

#[macro_export]
macro_rules! assert_debug_strings {
    ($expected:expr, $value:expr) => {{
        match (&$expected, &$value) {
            (expected_val, val) => {
                let mut strings = val.iter().map(|v| format!("{:?}", v));
                assert_eq!(*expected_val, strings.join("\n"))
            }
        }
    }};
    ($expected:expr, $value:expr ,) => {
        $crate::assert_debug_strings!($expected, $value)
    };
}
