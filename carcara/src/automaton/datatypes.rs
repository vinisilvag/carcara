use std::collections::HashSet;

pub struct State {
    accept: bool,
    id: usize,
    transitions: HashSet<Transition>
}

impl State {
    fn new(accept: bool, id: usize) -> Self {
        State {
            accept,
            id,
            transitions: HashSet::new()
        }
    }
}

pub struct Transition {
    min: usize,
    max: usize,
    to: State
}

impl Transition {
    fn new(min: usize, max: usize, to: State) -> Self {
        Transition {
            min,
            max,
            to
        }
    }
}