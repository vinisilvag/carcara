use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
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
pub enum Trigger {
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
        transitions_vec.sort_by(|a, b| a.to.cmp(&b.to).then_with(|| a.trigger.cmp(&b.trigger)));
        for transition in transitions_vec {
            transition.hash(state);
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Transition {
    to: StateId,
    trigger: Trigger,
}

impl Transition {
    fn new(state_id: StateId, trigger: Trigger) -> Transition {
        Transition { to: state_id, trigger }
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

        for (from, to, trigger) in transitions.clone() {
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
                        .insert(Transition::new(transition_ids[1], Trigger::Range(trigger)));
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
                if transition.trigger == Trigger::Epsilon {
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

    fn epsilon_closure(&self, states: &HashSet<StateId>) -> HashSet<StateId> {
        let mut closure = states.clone();
        let mut stack: Vec<StateId> = states.iter().copied().collect();

        while let Some(current) = stack.pop() {
            let state = self.get_state(current);
            for t in &state.transitions {
                if t.trigger == Trigger::Epsilon && !closure.contains(&t.to) {
                    closure.insert(t.to);
                    stack.push(t.to);
                }
            }
        }

        closure
    }

    fn symbol_triggers(&self) -> HashSet<Trigger> {
        self.all_states
            .iter()
            .flat_map(|s| s.transitions.iter())
            .filter(|t| t.trigger != Trigger::Epsilon)
            .map(|t| t.trigger.clone())
            .collect()
    }

    pub fn nfa_to_dfa(&self) -> Automata {
        let triggers = self.symbol_triggers();
        let start_closure: BTreeSet<usize> = self
            .epsilon_closure(&HashSet::from([self.initial_state]))
            .into_iter()
            .collect();

        let mut new_states: Vec<State> = Vec::new();
        let mut state_map: HashMap<BTreeSet<StateId>, StateId> = HashMap::new();
        let mut queue: VecDeque<BTreeSet<StateId>> = VecDeque::new();

        let mut next_id: StateId = 0;
        state_map.insert(start_closure.clone(), next_id);
        queue.push_back(start_closure.clone());
        next_id += 1;

        while let Some(current_set) = queue.pop_front() {
            let current_id = state_map[&current_set];

            // Estado de aceitação: se algum estado do conjunto for de aceitação
            let accept = current_set.iter().any(|&sid| self.get_state(sid).accept);

            let mut transitions = HashSet::new();

            // Para cada símbolo (não-ε)
            for trigger in &triggers {
                let mut reachable = HashSet::new();

                // Estados alcançáveis lendo esse símbolo
                for &sid in &current_set {
                    let state = self.get_state(sid);
                    for t in &state.transitions {
                        if &t.trigger == trigger {
                            reachable.insert(t.to);
                        }
                    }
                }

                // Fecho-ε dos alcançáveis
                let next_closure = self.epsilon_closure(&reachable);
                if next_closure.is_empty() {
                    continue;
                }

                // Verifica se já existe no DFA
                let next_state_id = *state_map
                    .entry(next_closure.clone().into_iter().collect())
                    .or_insert_with(|| {
                        let id = next_id;
                        next_id += 1;
                        queue.push_back(next_closure.clone().into_iter().collect());
                        id
                    });

                // Adiciona a transição
                transitions.insert(Transition {
                    to: next_state_id,
                    trigger: trigger.clone(),
                });
            }

            new_states.push(State {
                id: current_id.to_string(),
                accept,
                transitions,
            });
        }

        Automata {
            name: format!("{}_dfa", self.name),
            all_states: new_states,
            initial_state: 0,
        }
    }

    pub fn complement(&self) -> Automata {
        let alphabet: HashSet<Trigger> = self.symbol_triggers();
        let mut new_states = self.all_states.clone();

        // Create sink state
        let sink_id = new_states.len();
        let sink = State {
            id: format!("sink"),
            accept: false,
            transitions: alphabet
                .iter()
                .map(|tr| Transition::new(sink_id, tr.clone()))
                .collect(),
        };
        new_states.push(sink);

        for state in &mut new_states {
            let seen: HashSet<Trigger> = state
                .transitions
                .iter()
                .map(|t| t.trigger.clone())
                .collect();

            for tr in &alphabet {
                if !seen.contains(tr) {
                    state
                        .transitions
                        .insert(Transition::new(sink_id, tr.clone()));
                }
            }
        }

        for state in &mut new_states {
            state.accept = !state.accept;
        }

        Automata {
            name: format!("{}_complement", self.name),
            all_states: new_states,
            initial_state: self.initial_state,
        }
    }

    pub fn create_from_regex_operators(
        pool: &mut dyn TermPool,
        t: &Rc<Term>,
    ) -> Result<Automata, CheckerError> {
        fn rec_create_from_regex_operators(
            pool: &mut dyn TermPool,
            t: &Rc<Term>,
        ) -> Result<Automata, CheckerError> {
            match t.as_ref() {
                Term::Op(Operator::ReKleeneClosure, r) => {
                    let r = r.first().unwrap();
                    let a = rec_create_from_regex_operators(pool, r)?;
                    let mut states = a.clone().all_states;

                    let new_init_id = states.len();

                    // handle initial state
                    states.push(State {
                        id: "new_init".to_owned(),
                        accept: true,
                        transitions: HashSet::from([Transition {
                            to: a.initial_state,
                            trigger: Trigger::Epsilon,
                        }]),
                    });

                    // handle accepting states
                    for i in 0..a.all_states.len() {
                        if states[i].accept {
                            states[i].transitions.insert(Transition {
                                to: a.initial_state,
                                trigger: Trigger::Epsilon,
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
                    let kleene_closure =
                        pool.add(Term::Op(Operator::ReKleeneClosure, vec![r.clone()]));
                    let equiv = pool.add(Term::Op(
                        Operator::ReConcat,
                        vec![r.clone(), kleene_closure],
                    ));
                    Ok(rec_create_from_regex_operators(pool, &equiv)?)
                }
                Term::Op(Operator::ReConcat, r) => {
                    let mut automatons: Vec<Automata> = Vec::new();
                    for regex in r {
                        automatons.push(rec_create_from_regex_operators(pool, regex)?)
                    }

                    let mut states: Vec<State> = automatons.first().unwrap().all_states.clone();
                    let new_initial_state = automatons.first().unwrap().initial_state;
                    let offset = states.len();

                    for state in states.iter_mut() {
                        if state.accept {
                            state.transitions.insert(Transition {
                                to: automatons[1].initial_state + offset,
                                trigger: Trigger::Epsilon,
                            });
                        }
                        state.accept = false;
                    }

                    let mut concat_states = automatons[1].all_states.clone();
                    for state in concat_states.iter_mut() {
                        for transition in state.transitions.clone() {
                            let new_transition = transition.clone();
                            state.transitions.remove(&transition);
                            state.transitions.insert(Transition {
                                to: new_transition.to + offset,
                                trigger: new_transition.trigger,
                            });
                        }
                    }

                    states.extend(concat_states);

                    Ok(Automata {
                        name: "re_concat".to_owned(),
                        all_states: states,
                        initial_state: new_initial_state,
                    })
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
                            trigger: Trigger::Range((
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
                                trigger: Trigger::Range((c.clone() as u32, c.clone() as u32)),
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
                Term::Const(Constant::RegLan(_, a)) => Ok(a.clone()),
                // TODO: change later
                _ => {
                    println!("sera");
                    Err(CheckerError::Unspecified)
                }
            }
        }

        Ok(rec_create_from_regex_operators(pool, t)?)
    }

    // pub fn create_from_string_operators(
    //     pool: &mut dyn TermPool,
    //     t: &Rc<Term>,
    // ) -> Result<Automata, CheckerError> {
    //     fn rec_create_from_string_operators(
    //         pool: &mut dyn TermPool,
    //         t: &Rc<Term>,
    //     ) -> Result<Rc<Term>, CheckerError> {
    //         match t.as_ref() {
    //             Term::Op(Operator::StrConcat, s) => {}
    //             _ => Ok(t.clone()),
    //         }
    //     }
    //
    //     let equivalent_regex_term = rec_create_from_string_operators(pool, t)?;
    //     Ok(Automata::create_from_regex_operators(
    //         pool,
    //         &equivalent_regex_term,
    //     )?)
    // }
}

// TODO: improve automata display later
impl fmt::Display for Automata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn hs<I: IntoIterator<Item = StateId>>(iter: I) -> HashSet<StateId> {
        iter.into_iter().collect()
    }

    fn make_state(id: StateId, transitions: &[(StateId, Trigger)]) -> State {
        State {
            id: id.to_string(),
            accept: false,
            transitions: transitions
                .iter()
                .cloned()
                .map(|(to, trigger)| Transition { to, trigger })
                .collect(),
        }
    }

    #[test]
    fn epsilon_closure_single_state_no_epsilon() {
        // Estado 0 sem transições ε
        let s0 = make_state(0, &[]);
        let nfa = Automata {
            name: "no_epsilon".into(),
            all_states: vec![s0],
            initial_state: 0,
        };

        let closure = nfa.epsilon_closure(&hs([0]));
        assert_eq!(closure, hs([0]));
    }

    #[test]
    fn epsilon_closure_simple_chain() {
        // 0 --ε--> 1 --ε--> 2
        let s0 = make_state(0, &[(1, Trigger::Epsilon)]);
        let s1 = make_state(1, &[(2, Trigger::Epsilon)]);
        let s2 = make_state(2, &[]);
        let nfa = Automata {
            name: "chain".into(),
            all_states: vec![s0, s1, s2],
            initial_state: 0,
        };

        let closure = nfa.epsilon_closure(&hs([0]));
        assert_eq!(closure, hs([0, 1, 2]));
    }

    #[test]
    fn epsilon_closure_with_cycle() {
        // 0 --ε--> 1 --ε--> 2 --ε--> 0 (ciclo)
        let s0 = make_state(0, &[(1, Trigger::Epsilon)]);
        let s1 = make_state(1, &[(2, Trigger::Epsilon)]);
        let s2 = make_state(2, &[(0, Trigger::Epsilon)]);
        let nfa = Automata {
            name: "cycle".into(),
            all_states: vec![s0, s1, s2],
            initial_state: 0,
        };

        let closure = nfa.epsilon_closure(&hs([0]));

        // Deve incluir todos os estados e não entrar em loop
        assert_eq!(closure, hs([0, 1, 2]));
    }

    fn epsilon_closure_multiple_start_states() {
        // 0 --ε--> 1, 2 sem conexão
        let s0 = make_state(0, &[(1, Trigger::Epsilon)]);
        let s1 = make_state(1, &[]);
        let s2 = make_state(2, &[]);
        let nfa = Automata {
            name: "multi_start".into(),
            all_states: vec![s0, s1, s2],
            initial_state: 0,
        };

        // Fecho-ε de {0,2} deve conter {0,1,2}
        let closure = nfa.epsilon_closure(&hs([0, 2]));
        assert_eq!(closure, hs([0, 1, 2]));
    }

    #[test]
    fn test_nfa_to_dfa_conversion() {}
}
