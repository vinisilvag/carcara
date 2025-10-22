use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::ast::{Constant, Operator, Rc, Term, TermPool};
use crate::checker::error::CheckerError;

pub mod dsu;
pub mod operations;
pub mod parser;
pub mod utils;

pub type StateId = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TransitionType {
    Epsilon,
    Range((u32, u32)),
}

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
    range: TransitionType,
}

impl Transition {
    fn new(state_id: StateId, range: TransitionType) -> Transition {
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
                    state.transitions.insert(Transition::new(
                        transition_ids[1],
                        TransitionType::Range(range),
                    ));
                }
            }
        }

        Automata {
            name: automata_name.to_string(),
            initial_state,
            all_states,
        }
    }

    pub fn is_nfa(&self) -> bool {
        for state in &self.all_states {
            for transition in &state.transitions {
                if transition.range == TransitionType::Epsilon {
                    return true;
                }
            }
        }
        false
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

    pub fn create_from_operators(
        pool: &mut dyn TermPool,
        t: &Rc<Term>,
    ) -> Result<Automata, CheckerError> {
        fn rec_create_from_operators(
            pool: &mut dyn TermPool,
            t: &Rc<Term>,
        ) -> Result<Automata, CheckerError> {
            match t.as_ref() {
                Term::Op(Operator::ReKleeneClosure, r) => {
                    let r = r.first().unwrap();
                    let a = rec_create_from_operators(pool, r)?;
                    let mut states = a.clone().all_states;

                    let new_init_id = states.len();

                    // handle initial state
                    states.push(State {
                        id: "new_init".to_owned(),
                        accept: true,
                        transitions: HashSet::from([Transition {
                            to: a.initial_state,
                            range: TransitionType::Epsilon,
                        }]),
                    });

                    // handle accepting states
                    for i in 0..a.all_states.len() {
                        if states[i].accept {
                            states[i].transitions.insert(Transition {
                                to: a.initial_state,
                                range: TransitionType::Epsilon,
                            });
                        }
                    }

                    Ok(Automata {
                        name: "re_kleene_closure".to_string(),
                        all_states: states,
                        initial_state: new_init_id,
                    })
                }
                Term::Op(Operator::ReKleeneCross, r) => {
                    let r = r.first().unwrap();
                    let closure = pool.add(Term::Op(Operator::ReKleeneClosure, vec![r.clone()]));
                    let equiv = pool.add(Term::Op(Operator::ReConcat, vec![r.clone(), closure]));
                    Ok(rec_create_from_operators(pool, &equiv)?)
                }
                Term::Op(Operator::ReConcat, r) => {
                    let mut automatons: Vec<Automata> = Vec::new();
                    for regex in r {
                        automatons.push(rec_create_from_operators(pool, regex)?)
                    }
                    // let mut states = automatons.first().unwrap().all_states;
                    // for index in 1..automatons.len() {}
                    Err(CheckerError::Unspecified)
                }
                Term::Op(Operator::StrToRe, s) => {
                    let s = s.first().unwrap();
                    let Term::Const(Constant::String(s)) = s.as_ref() else {
                        // TODO: change later
                        return Err(CheckerError::Unspecified);
                    };

                    let characters: Vec<char> = s.chars().collect();
                    let first_char = characters.first().unwrap();
                    let offset = 1;

                    let mut states: Vec<State> = Vec::new();
                    states.push(State {
                        id: "init".to_string(),
                        accept: false,
                        transitions: HashSet::from([Transition {
                            to: 1,
                            range: TransitionType::Range((
                                first_char.clone() as u32,
                                first_char.clone() as u32,
                            )),
                        }]),
                    });

                    for (index, c) in characters.iter().enumerate() {
                        let mut transitions = HashSet::new();
                        if index != characters.len() - 1 {
                            transitions.insert(Transition {
                                to: index + offset + 1,
                                range: TransitionType::Range((c.clone() as u32, c.clone() as u32)),
                            });
                        }
                        states.push(State {
                            id: c.to_string(),
                            accept: index == characters.len() - 1,
                            transitions,
                        });
                    }
                    Ok(Automata {
                        name: "str_to_re".to_owned(),
                        all_states: states,
                        initial_state: 0,
                    })
                }
                // TODO: change later
                _ => Err(CheckerError::Unspecified),
            }
        }

        rec_create_from_operators(pool, t)
    }

    // (re.inter (str.to_re "abc") (re.++ ...))

    // pub fn empty() -> Self { /* re.none */
    // }

    // pub fn all() -> Self { /* re.all */
    // }

    // pub fn allchar() -> Self { /* re.allchar */
    // }

    // pub fn from_literal(s: &str) -> Self { /* str.to_re */
    // }

    // pub fn concat(a: &Self, b: &Self) -> Self { /* re.++ */
    // }

    // pub fn union(a: &Self, b: &Self) -> Self { /* re.union */
    // }

    // // fazer assim, recebendo, criando a referencia mutavel internamente e retornando depois
    // fn intersection(self, other: Self) -> Self {
    //     // ver se é isso mesmo depois
    //     let mut other = other;
    //     // ...
    // }

    // pub fn star(a: &Self) -> Self { /* re.* */
    // }
}

// TODO: improve automata display later
impl fmt::Display for Automata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}
