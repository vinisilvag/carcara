pub mod dsu;
// pub mod operations;
pub mod parser;
pub mod utils;

// use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};

// use crate::ast::{Constant, Operator, Rc, Term, TermPool};
use crate::automata::utils::{has_overlapping_ranges, missing_ranges};
// use crate::checker::error::CheckerError;

/// Type alias for state representation.
pub type StateId = usize;

/// Condition under which a transition is enabled.
///
/// A trigger may either consume no input (epsilon transition) or
/// consume a single input symbol whose value lies within a given range.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Trigger {
    /// Epsilon transition (does not consume input).
    Epsilon,

    /// Transition enabled by any input symbol in the inclusive range [l, r].
    Range((u32, u32)),
}

impl Trigger {
    /// Returns true if `self` covers `other`
    pub fn contains(&self, other: &Trigger) -> bool {
        match (self, other) {
            (Trigger::Epsilon, Trigger::Epsilon) => true,
            (Trigger::Range((a_start, a_end)), Trigger::Range((b_start, b_end))) => {
                a_start <= b_start && b_end <= a_end
            }
            (Trigger::Range((_, _)), Trigger::Epsilon) => false,
            (Trigger::Epsilon, Trigger::Range((_, _))) => false,
        }
    }
}

impl fmt::Display for Trigger {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Epsilon => {
                write!(f, "ε")
            }
            Self::Range((l, r)) => {
                write!(f, "({}, {})", l, r)
            }
        }
    }
}

/// Represents a state in the automaton.
///
/// A state is identified by a symbolic identifier, may be marked as accepting,
/// and defines a set of outgoing transitions labeled by triggers.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    /// State symbolic name.
    id: String,

    /// Accepting state or not.
    accept: bool,

    /// Set of outgoing transitions.
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

impl Hash for State {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut transitions_vec: Vec<_> = self.transitions.iter().collect();
        transitions_vec.sort_by(|a, b| a.to.cmp(&b.to).then_with(|| a.trigger.cmp(&b.trigger)));
        for transition in transitions_vec {
            transition.hash(state);
        }
    }
}

/// Represents a transition between automaton states.
///
/// A transition leads from the enclosing source state to a destination state
/// and is labeled by a trigger describing which input symbols enable it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Transition {
    /// Identifier of the destination state.
    to: StateId,

    /// Label of the transition, describing the consumed input.
    trigger: Trigger,
}

impl Transition {
    fn new(state_id: StateId, trigger: Trigger) -> Transition {
        Transition { to: state_id, trigger }
    }
}

/// Represents a finite automaton.
///
/// An `Automaton` value defines the structure of a (possibly nondeterministic)
/// finite automaton with epsilon transitions. It consists of:
///
///  - a symbolic name identifying the automaton;
///  - a finite set of states, stored in `all_states`;
///  - a distinguished initial state, identified by `initial_state`.
///
/// States are indexed by their position in `all_states`. Transitions refer to
/// destination states via these indices (`StateId`), forming a directed graph.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Automaton {
    /// Automaton symbolic name.
    name: String,

    /// Finite collection of states forming the automaton.
    all_states: Vec<State>,

    /// Identifier of the initial state.
    initial_state: StateId,
}

impl Automaton {
    // Construct an automaton based on the automaton name, initial state id, the complete set of
    // transitions (from, to, range), and the set of accepting states
    fn new(
        automaton_name: &str,
        initial_state_id: &str,
        transitions: Vec<(&str, &str, (u32, u32))>,
        accepting_states: Vec<&str>,
    ) -> Automaton {
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

        for (from, to, trigger) in transitions.clone() {
            let mut transition_ids: Vec<StateId> = Vec::new();

            // Create the state if it does not exists
            for id in [from, to] {
                let mut found: Option<StateId> = None;
                for (index, state) in all_states.iter().enumerate() {
                    if state.id == id.to_owned() {
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
                        .insert(Transition::new(transition_ids[1], Trigger::Range(trigger)));
                }
            }
        }

        Automaton {
            name: automaton_name.to_owned(),
            initial_state,
            all_states,
        }
    }

    pub fn is_nfa(&self) -> bool {
        for state in &self.all_states {
            let mut ranges = Vec::new();
            for transition in &state.transitions {
                match transition.trigger {
                    Trigger::Range(range) => {
                        ranges.push(range);
                    }
                    Trigger::Epsilon => {
                        return true;
                    }
                };
            }
            // NFA if the automaton has overlapping ranges on transitions outgoing the same state
            // (non-determinism)
            if has_overlapping_ranges(ranges.clone()) {
                return true;
            }
            // NFA if the automaton does not have transitions for every range from 0 to 255
            if !missing_ranges(&ranges, 0, 255).is_empty() {
                return true;
            }
        }
        false
    }

    pub fn get_state(&self, state_id: StateId) -> &State {
        &self.all_states[state_id]
    }

    pub fn get_state_transitions(&self, state_id: StateId) -> HashSet<Transition> {
        let state = &self.all_states[state_id];
        state.transitions.clone()
    }

    pub fn get_accepting_states(&self) -> Vec<State> {
        let mut states = Vec::new();
        for state in &self.all_states {
            if state.accept {
                states.push(state.clone());
            }
        }
        states
    }

    pub fn get_all_transitions(&self) -> Vec<(State, State, Trigger)> {
        let mut transitions: Vec<(State, State, Trigger)> = Vec::new();
        for state in &self.all_states {
            for transition in &state.transitions {
                transitions.push((
                    state.clone(),
                    self.get_state(transition.to).clone(),
                    transition.trigger.clone(),
                ));
            }
        }
        transitions
    }

    pub fn get_initial_state(&self) -> State {
        self.get_state(self.initial_state).clone()
    }
}
