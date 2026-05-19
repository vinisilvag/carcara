pub mod dsu;
pub mod operations;
pub mod parser;
pub mod utils;

use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::hash::{Hash, Hasher};

use crate::ast::{Constant, Operator, Rc, Term, TermPool};
use crate::automata::utils::{has_overlapping_ranges, missing_ranges};
use crate::checker::error::CheckerError;

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
    Range((u16, u16)),
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
        transitions: Vec<(&str, &str, (u16, u16))>,
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
            // NFA if the automaton does not have transitions for every range from 0 to u16::MAX
            if !missing_ranges(&ranges, 0, u16::MAX).is_empty() {
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

    // Returns the set of states the can be reached by every state in the automaton following any
    // number of Epsilon transitions
    fn epsilon_closure(start: &BTreeSet<StateId>, a: &Automaton) -> BTreeSet<StateId> {
        let mut stack: Vec<StateId> = start.iter().cloned().collect();
        let mut closure = start.clone();

        while let Some(s) = stack.pop() {
            for t in &a.all_states[s].transitions {
                if t.trigger == Trigger::Epsilon {
                    if !closure.contains(&t.to) {
                        closure.insert(t.to);
                        stack.push(t.to);
                    }
                }
            }
        }

        closure
    }

    fn partition_ranges(edges: &Vec<(u16, u16, StateId)>) -> Vec<((u16, u16), BTreeSet<StateId>)> {
        let mut points = Vec::new();

        for (l, r, _) in edges {
            points.push(*l);
            if *r < u16::MAX {
                points.push(r + 1);
            }
        }

        points.sort();
        points.dedup();

        let mut result = Vec::new();

        for w in points.windows(2) {
            let a = w[0];
            let b = w[1] - 1;

            let mut dests = BTreeSet::new();

            for (l, r, to) in edges {
                if *l <= a && *r >= b {
                    dests.insert(*to);
                }
            }
            if !dests.is_empty() {
                result.push(((a, b), dests));
            }
        }

        result
    }

    // Set of all triggers in the automaton
    // Used to get the effective alphabet of the automaton
    fn symbol_triggers(&self) -> HashSet<Trigger> {
        self.all_states
            .iter()
            .flat_map(|s| s.transitions.iter())
            .filter(|t| t.trigger != Trigger::Epsilon)
            .map(|t| t.trigger.clone())
            .collect()
    }

    pub fn determinize(nfa: &Automaton) -> Automaton {
        let mut new_states: Vec<State> = Vec::new();
        let mut state_map: HashMap<BTreeSet<StateId>, StateId> = HashMap::new();
        let mut queue = VecDeque::new();

        let mut init = BTreeSet::new();
        init.insert(nfa.initial_state);
        let init_closure = Automaton::epsilon_closure(&init, nfa);

        let init_accept = init_closure.iter().any(|&s| nfa.all_states[s].accept);

        new_states.push(State {
            id: "D0".to_string(),
            accept: init_accept,
            transitions: HashSet::new(),
        });

        state_map.insert(init_closure.clone(), 0);
        queue.push_back(init_closure);

        // Subset construction
        while let Some(current_set) = queue.pop_front() {
            let current_id = *state_map.get(&current_set).unwrap();

            let mut edges: Vec<(u16, u16, StateId)> = Vec::new();

            for s in &current_set {
                for t in &nfa.all_states[*s].transitions {
                    if let Trigger::Range((l, r)) = t.trigger {
                        edges.push((l, r, t.to));
                    }
                }
            }

            let parts = Automaton::partition_ranges(&edges);

            for ((l, r), dests) in parts {
                let closure = Automaton::epsilon_closure(&dests, nfa);

                let dest_id = if let Some(id) = state_map.get(&closure) {
                    *id
                } else {
                    let new_id = new_states.len();
                    let accept = closure.iter().any(|&s| nfa.all_states[s].accept);

                    new_states.push(State {
                        id: format!("D{}", new_id),
                        accept,
                        transitions: HashSet::new(),
                    });

                    state_map.insert(closure.clone(), new_id);
                    queue.push_back(closure);
                    new_id
                };

                new_states[current_id].transitions.insert(Transition {
                    to: dest_id,
                    trigger: Trigger::Range((l, r)),
                });
            }
        }

        // Sink state and complete transitions
        let sink_id = new_states.len();

        new_states.push(State {
            id: format!("D{}", sink_id),
            accept: false,
            transitions: HashSet::new(),
        });

        for i in 0..sink_id {
            let mut covered = vec![false; u16::MAX as usize + 1];

            for t in new_states[i].transitions.clone() {
                if let Trigger::Range((l, r)) = t.trigger {
                    for c in l as usize..=r.min(u16::MAX) as usize {
                        covered[c] = true;
                    }
                }
            }

            let mut start = None;

            for c in 0..=u16::MAX {
                if !covered[c as usize] && start.is_none() {
                    start = Some(c as u16);
                }
                if covered[c as usize] && start.is_some() {
                    let l = start.unwrap();
                    let r = (c as u16) - 1;
                    new_states[i].transitions.insert(Transition {
                        to: sink_id,
                        trigger: Trigger::Range((l, r)),
                    });
                    start = None;
                }
            }

            if let Some(l) = start {
                new_states[i].transitions.insert(Transition {
                    to: sink_id,
                    trigger: Trigger::Range((l, u16::MAX)),
                });
            }
        }

        // Sink loop
        new_states[sink_id].transitions.insert(Transition {
            to: sink_id,
            trigger: Trigger::Range((0, u16::MAX)),
        });

        Automaton {
            name: format!("{}_dfa", nfa.name),
            all_states: new_states,
            initial_state: 0,
        }
    }

    pub fn complement(&self) -> Automaton {
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

        Automaton {
            name: format!("{}_complement", self.name),
            all_states: new_states,
            initial_state: self.initial_state,
        }
    }

    pub fn create_from_regex_operators(
        pool: &mut dyn TermPool,
        t: &Rc<Term>,
    ) -> Result<Automaton, CheckerError> {
        fn shift_states(states: Vec<State>, shift: usize) -> Vec<State> {
            let mut new_states = states.clone();
            for state in new_states.iter_mut() {
                for transition in state.transitions.clone() {
                    let new_transition = transition.clone();
                    state.transitions.remove(&transition);
                    state.transitions.insert(Transition {
                        to: new_transition.to + shift,
                        trigger: new_transition.trigger,
                    });
                }
            }
            new_states
        }

        fn rec_create_from_regex_operators(
            pool: &mut dyn TermPool,
            t: &Rc<Term>,
        ) -> Result<Automaton, CheckerError> {
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

                    Ok(Automaton {
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
                    let mut automatons: Vec<Automaton> = Vec::new();
                    for regex in r {
                        let a = rec_create_from_regex_operators(pool, regex)?;
                        if operations::has_reachable_accepting_state(a.clone()) {
                            automatons.push(a);
                        }
                    }

                    if automatons.len() == 1 {
                        return Ok(automatons.first().unwrap().clone());
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

                    Ok(Automaton {
                        name: "re_concat".to_owned(),
                        all_states: states,
                        initial_state: new_initial_state,
                    })
                }
                Term::Op(Operator::StrToRe, s) => {
                    let s = s.first().unwrap();
                    let Term::Const(Constant::String(s)) = s.as_ref() else {
                        return Err(CheckerError::ExpectedStringConstantInsideStrToRe(s.clone()));
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
                                first_char.clone() as u16,
                                first_char.clone() as u16,
                            )),
                        }]),
                    });

                    for (index, c) in characters.iter().enumerate() {
                        let mut transitions = HashSet::new();
                        if index != characters.len() - 1 {
                            transitions.insert(Transition {
                                to: index + offset + 1,
                                trigger: Trigger::Range((c.clone() as u16, c.clone() as u16)),
                            });
                        }
                        states.push(State {
                            id: c.to_string(),
                            accept: index == characters.len() - 1,
                            transitions,
                        });
                    }

                    Ok(Automaton {
                        name: "str_to_re".to_owned(),
                        all_states: states,
                        initial_state: 0,
                    })
                }
                Term::Op(Operator::ReNone, _) => {
                    let mut states: Vec<State> = Vec::new();
                    states.push(State {
                        id: "init".to_string(),
                        accept: false,
                        transitions: HashSet::from_iter(
                            [Transition {
                                to: 0,
                                trigger: Trigger::Range((0, u16::MAX)),
                            }]
                            .iter()
                            .cloned(),
                        ),
                    });
                    Ok(Automaton {
                        name: "re_none".to_owned(),
                        all_states: states,
                        initial_state: 0,
                    })
                }
                Term::Op(Operator::ReIntersection, inter) => {
                    let mut components = Vec::new();
                    for re in inter {
                        let nfa = rec_create_from_regex_operators(pool, &re)?;
                        components.push(Automaton::determinize(&nfa));
                    }
                    let mut res =
                        operations::intersection(components[0].clone(), components[1].clone())?;
                    for index in 2..components.len() {
                        res = operations::intersection(res, components[index].clone())?;
                    }
                    Ok(res)
                }
                Term::Op(Operator::ReUnion, uni) => {
                    let mut automata: Vec<Automaton> = Vec::new();
                    for re in uni {
                        automata.push(rec_create_from_regex_operators(pool, &re)?);
                    }

                    let mut states: Vec<State> = Vec::new();
                    let mut transitions: HashSet<Transition> = HashSet::new();
                    let mut index = 1;
                    for automaton in automata {
                        states.extend(shift_states(automaton.all_states.clone(), states.len() + 1));
                        transitions.insert(Transition {
                            to: index,
                            trigger: Trigger::Epsilon,
                        });
                        index += automaton.all_states.len();
                    }

                    states.insert(
                        0,
                        State {
                            id: "init".to_string(),
                            accept: false,
                            transitions,
                        },
                    );

                    Ok(Automaton {
                        name: "re_union".to_owned(),
                        all_states: states,
                        initial_state: 0,
                    })
                }
                Term::Const(Constant::RegLan(_, a)) => Ok(a.clone()),
                _ => Err(CheckerError::UnexpectedTermOnAutomatonConversion(t.clone())),
            }
        }

        Ok(rec_create_from_regex_operators(pool, t)?)
    }
}

// TODO: improve automaton display later
impl fmt::Display for Automaton {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}
