use crate::chase::chase::StrategyNode;
use crate::chase::chase::Strategy;
use crate::chase::chase::Model;
use crate::chase::chase::Selector;
use crate::chase::chase::Sequent;
use std::collections::VecDeque;

pub struct FIFO<S:Sequent, M:Model, Sel: Selector<Item=S>> {
    queue: VecDeque<StrategyNode<S, M, Sel>>
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> FIFO<S, M, Sel> {
    pub fn new() -> FIFO<S, M, Sel> {
        FIFO { queue: VecDeque::new() }
    }
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> Strategy<S, M, Sel> for FIFO<S, M, Sel> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, node: StrategyNode<S, M, Sel>) {
        self.queue.push_back(node)
    }

    fn remove(&mut self) -> Option<StrategyNode<S, M, Sel>> {
        self.queue.pop_front()
    }
}

pub struct LIFO<S:Sequent, M:Model, Sel: Selector<Item=S>> {
    queue: VecDeque<StrategyNode<S, M, Sel>>
}

impl<S: Sequent, M: Model, Sel: Selector<Item=S>> Strategy<S, M, Sel> for LIFO<S, M, Sel> {
    fn empty(&self) -> bool {
        self.queue.is_empty()
    }

    fn add(&mut self, node: StrategyNode<S, M, Sel>) {
        self.queue.push_front(node)
    }

    fn remove(&mut self) -> Option<StrategyNode<S, M, Sel>> {
        self.queue.pop_front()
    }
}