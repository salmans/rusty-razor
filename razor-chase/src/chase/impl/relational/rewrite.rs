use std::{collections::HashMap, hash::Hash};

/// Implements a simple algorithm for reasoning about equality of elements by rewriting
/// equal elements to the same representative element of their equivalence class.
pub(super) struct Rewrite<T>
where
    T: PartialEq + Eq + Clone + Hash,
{
    /// Captures the set of rules in the form of mapping a key to a value element.
    rules: HashMap<T, T>,
}

impl<T> Rewrite<T>
where
    T: PartialEq + Eq + Clone + Hash,
{
    /// Creates a new `Rewrite` instance.
    pub fn new() -> Self {
        Self {
            rules: HashMap::new(),
        }
    }

    /// Adds a new equation as a rewrite rule from `left` to `right`.
    #[allow(clippy::or_fun_call)]
    pub fn rewrite(&mut self, left: &T, right: &T) {
        if self.equals(left, right) == Some(true) {
            return;
        }

        let left = self
            .rules
            .entry(left.clone())
            .or_insert(right.clone())
            .clone();
        let right = self
            .rules
            .entry(right.clone())
            .or_insert(right.clone())
            .clone();

        for v in self.rules.values_mut() {
            if *v == left {
                *v = right.clone()
            }
        }
    }

    /// Returns a `Some(true)` if `left` and `right` have the same normal form and `Some(false)` if different.
    /// It returns `None` if either of `left` or `right` does not have a normal form in the current set of rules.
    pub fn equals(&self, left: &T, right: &T) -> Option<bool> {
        let left = self.rules.get(left)?;
        let right = self.rules.get(right)?;

        Some(left == right)
    }

    /// Returns the normal form of `item` in the existing set of rules if it exists.
    pub fn normalize(&self, item: &T) -> Option<&T> {
        self.rules.get(item)
    }

    /// Returns a vector of all normal forms in the existing set of rules.
    pub fn normal_forms(&self) -> Vec<&T> {
        use itertools::Itertools;
        self.rules.values().unique().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let mut rewrite = Rewrite::new();
        rewrite.rewrite(&1, &11);
        rewrite.rewrite(&2, &22);

        assert_eq!(Some(true), rewrite.equals(&1, &11));
        assert_eq!(Some(false), rewrite.equals(&2, &11));
        assert_eq!(None, rewrite.equals(&2, &3));

        assert_eq!(Some(&11), rewrite.normalize(&1));
        assert_eq!(Some(&22), rewrite.normalize(&22));
        assert_eq!(None, rewrite.normalize(&3));
    }

    #[test]
    fn test_merge_classes() {
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&1, &111);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &111));
            assert_eq!(Some(true), rewrite.equals(&11, &111));

            assert_eq!(Some(&111), rewrite.normalize(&1));
            assert_eq!(Some(&111), rewrite.normalize(&11));
            assert_eq!(Some(&111), rewrite.normalize(&111));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&11, &111);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &111));
            assert_eq!(Some(true), rewrite.equals(&11, &111));

            assert_eq!(Some(&111), rewrite.normalize(&1));
            assert_eq!(Some(&111), rewrite.normalize(&11));
            assert_eq!(Some(&111), rewrite.normalize(&111));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&2, &22);
            rewrite.rewrite(&11, &111);

            assert_eq!(Some(false), rewrite.equals(&1, &22));
            assert_eq!(Some(false), rewrite.equals(&11, &22));
            assert_eq!(Some(false), rewrite.equals(&11, &22));
        }
    }

    #[test]
    fn test_merge_multiple_classes() {
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&2, &22);
            rewrite.rewrite(&1, &2);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&2, &22);
            rewrite.rewrite(&1, &22);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&2, &22);
            rewrite.rewrite(&2, &1);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&2, &22);
            rewrite.rewrite(&2, &11);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.rewrite(&1, &11);
            rewrite.rewrite(&2, &22);
            rewrite.rewrite(&11, &111);
            rewrite.rewrite(&2, &222);
            rewrite.rewrite(&1, &2);

            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
            assert_eq!(Some(true), rewrite.equals(&111, &222));
        }
    }
}
