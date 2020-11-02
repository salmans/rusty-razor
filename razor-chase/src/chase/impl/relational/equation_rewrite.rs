use std::{collections::HashMap, hash::Hash};

pub(super) struct Rewrite<T>
where
    T: PartialEq + Eq + Clone + Hash,
{
    rules: HashMap<T, T>,
}

impl<T> Rewrite<T>
where
    T: PartialEq + Eq + Clone + Hash,
{
    pub fn new() -> Self {
        Self {
            rules: HashMap::new(),
        }
    }

    #[allow(clippy::or_fun_call)]
    pub fn add(&mut self, left: &T, right: &T) {
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

        self.rules.iter_mut().for_each(|(_, v)| {
            if *v == left {
                *v = right.clone()
            }
        });
    }

    pub fn equals(&self, left: &T, right: &T) -> Option<bool> {
        let left = self.rules.get(left)?;
        let right = self.rules.get(right)?;

        Some(left == right)
    }

    pub fn canonical(&self, item: &T) -> Option<&T> {
        self.rules.get(item)
    }

    pub fn canonicals(&self) -> Vec<&T> {
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
        rewrite.add(&1, &11);
        rewrite.add(&2, &22);

        assert_eq!(Some(true), rewrite.equals(&1, &11));
        assert_eq!(Some(false), rewrite.equals(&2, &11));
        assert_eq!(None, rewrite.equals(&2, &3));

        assert_eq!(Some(&11), rewrite.canonical(&1));
        assert_eq!(Some(&22), rewrite.canonical(&22));
        assert_eq!(None, rewrite.canonical(&3));
    }

    #[test]
    fn test_merge_classes() {
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&1, &111);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &111));
            assert_eq!(Some(true), rewrite.equals(&11, &111));

            assert_eq!(Some(&111), rewrite.canonical(&1));
            assert_eq!(Some(&111), rewrite.canonical(&11));
            assert_eq!(Some(&111), rewrite.canonical(&111));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&11, &111);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &111));
            assert_eq!(Some(true), rewrite.equals(&11, &111));

            assert_eq!(Some(&111), rewrite.canonical(&1));
            assert_eq!(Some(&111), rewrite.canonical(&11));
            assert_eq!(Some(&111), rewrite.canonical(&111));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&2, &22);
            rewrite.add(&11, &111);

            assert_eq!(Some(false), rewrite.equals(&1, &22));
            assert_eq!(Some(false), rewrite.equals(&11, &22));
            assert_eq!(Some(false), rewrite.equals(&11, &22));
        }
    }

    #[test]
    fn test_merge_multiple_classes() {
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&2, &22);
            rewrite.add(&1, &2);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&2, &22);
            rewrite.add(&1, &22);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&2, &22);
            rewrite.add(&2, &1);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&2, &22);
            rewrite.add(&2, &11);

            assert_eq!(Some(true), rewrite.equals(&1, &11));
            assert_eq!(Some(true), rewrite.equals(&1, &22));
            assert_eq!(Some(true), rewrite.equals(&2, &11));
            assert_eq!(Some(true), rewrite.equals(&2, &22));
            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
        }
        {
            let mut rewrite = Rewrite::new();
            rewrite.add(&1, &11);
            rewrite.add(&2, &22);
            rewrite.add(&11, &111);
            rewrite.add(&2, &222);
            rewrite.add(&1, &2);

            assert_eq!(Some(true), rewrite.equals(&1, &2));
            assert_eq!(Some(true), rewrite.equals(&11, &22));
            assert_eq!(Some(true), rewrite.equals(&111, &222));
        }
    }
}
