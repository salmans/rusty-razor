//! A persistent union-find whose classes are represented by their smallest member.
use std::hash::Hash;

/// A persistent union-find. Only non-roots have a parent entry, and the representative of a
/// class is its smallest member, so a caller decides which member wins by ordering them.
#[derive(Clone)]
pub(super) struct UnionFind<T: Clone + Eq + Hash + Ord> {
    parent: im::HashMap<T, T>,
}

impl<T: Clone + Eq + Hash + Ord> Default for UnionFind<T> {
    fn default() -> Self {
        Self {
            parent: im::HashMap::new(),
        }
    }
}

impl<T: Clone + Eq + Hash + Ord> UnionFind<T> {
    /// The representative of the class of `t`.
    pub(super) fn find(&self, mut t: T) -> T {
        while let Some(p) = self.parent.get(&t) {
            t = p.clone();
        }
        t
    }

    /// Merges the classes of `a` and `b`; returns `(winner, loser)` if they were distinct.
    pub(super) fn union(&mut self, a: T, b: T) -> Option<(T, T)> {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return None;
        }
        let (winner, loser) = if ra < rb { (ra, rb) } else { (rb, ra) };
        self.parent.insert(loser.clone(), winner.clone());
        Some((winner, loser))
    }
}
