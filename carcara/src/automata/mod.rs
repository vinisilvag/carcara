use std::collections::HashSet;
use std::hash::{Hash, Hasher};

pub mod dsu;
pub mod operations;
pub mod parser;
pub mod utils;

pub type StateId = usize;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    id: String,
    accept: bool,
    transitions: HashSet<Transition>,
}

impl State {
    fn new(id: &str, accept: bool) -> State {
        State {
            id: id.to_owned(),
            accept,
            transitions: HashSet::new(),
        }
    }
}

// TODO: check later
impl Hash for State {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut transitions_vec: Vec<_> = self.transitions.iter().collect();
        transitions_vec.sort_by(|a, b| a.to.cmp(&b.to).then_with(|| a.range.cmp(&b.range)));
        for transition in transitions_vec {
            transition.hash(state);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Transition {
    to: StateId,
    range: (u32, u32),
}

impl Transition {
    fn new(state_id: StateId, range: (u32, u32)) -> Transition {
        Transition { to: state_id, range }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Automata {
    name: String,
    all_states: Vec<State>,
    initial_state: StateId,
}

impl Automata {
    fn new(
        automata_name: &str,
        initial_state_id: &str,
        transitions: Vec<(&str, &str, (u32, u32))>,
        accepting_states: Vec<&str>,
    ) -> Automata {
        let mut accepting_states_map = HashSet::new();
        for state in accepting_states.clone() {
            accepting_states_map.insert(state);
        }

        let initial_state: StateId = 0;
        let mut all_states: Vec<State> = Vec::new();
        all_states.push(State::new(
            initial_state_id,
            accepting_states_map.contains(initial_state_id),
        ));

        for (from, to, range) in transitions.clone() {
            let mut transition_ids: Vec<StateId> = Vec::new();

            // Create the state if it does not exists
            for id in [from, to] {
                let mut found: Option<StateId> = None;
                for (index, state) in all_states.iter().enumerate() {
                    if state.id == id.to_string() {
                        found = Some(index);
                        transition_ids.push(index);
                    }
                }
                if found.is_none() {
                    all_states.push(State::new(id, accepting_states_map.contains(id)));
                    transition_ids.push(all_states.len() - 1);
                }
            }

            // Handle transitions
            for state in &mut all_states {
                if state.id == from {
                    state
                        .transitions
                        .insert(Transition::new(transition_ids[1], range));
                }
            }
        }

        Automata {
            name: automata_name.to_string(),
            initial_state,
            all_states,
        }
    }

    pub fn get_state(&self, state_id: StateId) -> &State {
        let state = &self.all_states[state_id];
        return state;
    }

    pub fn get_state_transitions(&self, state_id: StateId) -> HashSet<Transition> {
        let state = &self.all_states[state_id];
        return state.transitions.clone();
    }

    pub fn get_transitions(&self) -> Vec<Transition> {
        let mut transitions: Vec<Transition> = Vec::new();
        for state in &self.all_states {
            transitions.extend(state.transitions.clone());
        }
        return transitions;
    }
}
