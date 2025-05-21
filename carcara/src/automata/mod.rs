use std::collections::HashSet;

pub mod parser;

#[derive(Debug)]
pub struct State {
    id: String,
    accept: bool,
    transitions: HashSet<Transition>,
}

impl State {
    pub fn set_accepting(&mut self) {
        self.accept = true;
    }
}

#[derive(Debug)]
pub struct Transition {
    to: State,
    range: (u32, u32),
}

#[derive(Debug)]
pub struct Automata {
    name: String,
    initial_state: State,
}

impl Automata {
    fn new(
        name: String,
        initial_state: State,
        transitions: Vec<Transition>,
        accepting_states: Vec<State>,
    ) -> Automata {
        println!("initial state {:?}", initial_state);
        println!("transitions {:?}", transitions);
        println!("accepting states {:?}", accepting_states);

        Automata { name, initial_state }
    }
}
