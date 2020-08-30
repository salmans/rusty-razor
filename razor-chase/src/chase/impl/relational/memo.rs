// use super::TupleE;
// use razor_fol::syntax::Pred;
// use relalg;
// use std::{collections::HashMap, hash::Hash};

// #[derive(PartialEq, Eq, Hash)]
// pub(crate) struct RelationProject {
//     pred: Pred,
//     indices: Vec<usize>,
// }

// impl RelationProject {
//     fn new(pred: Pred, indices: Vec<usize>) -> Self {
//         Self { pred, indices }
//     }
// }

// pub(crate) struct ViewMemo<K> {
//     map: HashMap<K, relalg::View<TupleE>>,
//     insert_closure: Box<dyn Fn(&K, &relalg::Database) -> relalg::View<TupleE>>,
// }

// impl<K> ViewMemo<K>
// where
//     K: Eq + Hash + Clone,
// {
//     fn exp(&mut self, item: &K, database: &relalg::Database) -> relalg::View<TupleE> {
//         match self.map.get(item) {
//             Some(v) => v.clone(),
//             None => {
//                 let v = (self.insert_closure)(item, database);
//                 self.map.insert(item.clone(), v.clone());
//                 v
//             }
//         }
//     }
// }
