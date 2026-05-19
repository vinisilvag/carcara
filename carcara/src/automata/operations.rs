use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    automata::{utils::totalize, State, Transition, Trigger},
    checker::error::CheckerError,
};

use super::{dsu::DSU, utils::intersect_ranges, Automaton, StateId};

pub fn has_reachable_accepting_state(a: Automaton) -> bool {
    let accepting_states: Vec<_> = a
        .all_states
        .iter()
        .enumerate()
        .filter(|(_, state)| state.accept)
        .collect();
    // Has accepting states? If no, the intersection is empty
    if accepting_states.is_empty() {
        return false;
    }

    // Checking reachability with a BFS
    let mut visited: Vec<bool> = vec![false; a.all_states.len()];
    let mut queue: VecDeque<StateId> = VecDeque::new();

    queue.push_back(a.initial_state);

    while !queue.is_empty() {
        let state = queue.pop_front().unwrap();
        visited[state] = true;
        for transition in &a.all_states[state].transitions {
            let next = transition.to;
            if !visited[next] {
                queue.push_back(next);
            }
        }
    }

    for (state_id, _) in accepting_states {
        if visited[state_id] {
            return true;
        }
    }

    false
}

pub fn intersection(a1: Automaton, a2: Automaton) -> Result<Automaton, CheckerError> {
    let mut new_states = Vec::new();
    let mut state_map = HashMap::new();
    let mut queue = VecDeque::new();

    let initial_pair = (a1.initial_state, a2.initial_state);
    state_map.insert(initial_pair, 0);
    queue.push_back(initial_pair);

    new_states.push(State {
        id: format!("{:?}", initial_pair),
        accept: a1.get_state(a1.initial_state).accept && a2.get_state(a2.initial_state).accept,
        transitions: HashSet::new(),
    });

    while let Some((s1, s2)) = queue.pop_front() {
        let curr_id = state_map[&(s1, s2)];

        for t1 in &a1.get_state(s1).transitions {
            for t2 in &a2.get_state(s2).transitions {
                if let Some(range) = intersect_ranges(t1.trigger.clone(), t2.trigger.clone())? {
                    let dest = (t1.to, t2.to);
                    let next_id = *state_map.entry(dest).or_insert_with(|| {
                        let id = new_states.len();
                        new_states.push(State {
                            id: format!("{:?}", dest),
                            accept: a1.all_states[t1.to].accept && a2.all_states[t2.to].accept,
                            transitions: HashSet::new(),
                        });
                        queue.push_back(dest);
                        id
                    });
                    new_states[curr_id]
                        .transitions
                        .insert(Transition::new(next_id, Trigger::Range(range)));
                }
            }
        }
    }

    Ok(Automaton {
        name: format!("({} ∩ {})", a1.name, a2.name),
        all_states: new_states,
        initial_state: 0,
    })
}

// Implementation of automata equivalence checking based on the Hopcroft-Karp algorithm,
// adapted for testing the equivalence of deterministic finite automata (DFAs), as described
// in the paper "A Linear Algorithm for Testing Equivalence of Finite Automata".
pub fn is_equivalent(a1: Automaton, a2: Automaton) -> bool {
    let offset = a1.all_states.len();

    let accepting_states: Vec<StateId> = a1
        .all_states
        .iter()
        .enumerate()
        .filter_map(|(i, state)| state.accept.then_some(i))
        .chain(
            a2.all_states
                .iter()
                .enumerate()
                .filter_map(|(i, state)| state.accept.then_some(offset + i)),
        )
        .collect();

    // DSU work with StateId's
    let mut dsu = DSU::new(a1.all_states.len() + a2.all_states.len());

    // Stack work with StateId's
    let mut stack: VecDeque<(StateId, StateId)> = VecDeque::new();
    stack.push_front((a1.initial_state, a2.initial_state + offset));

    while let Some((s1, s2)) = stack.pop_front() {
        if accepting_states.contains(&s1) != accepting_states.contains(&s2) {
            return false;
        }

        let s1_transitions = a1.get_state_transitions(s1);
        let s2_transitions = a2.get_state_transitions(s2 - offset);

        // Every symbol in Σ (ranges)
        let ranges: HashSet<_> = HashSet::from_iter(
            s1_transitions
                .iter()
                .map(|t| t.trigger.clone())
                .chain(s2_transitions.iter().map(|t| t.trigger.clone()))
                .collect::<Vec<_>>(),
        );
        for range in &ranges {
            let s1_to: Option<StateId> = s1_transitions
                .iter()
                .find(|t| t.trigger == *range)
                .map(|t| t.to);
            let s2_to: Option<StateId> = s2_transitions
                .iter()
                .find(|t| t.trigger == *range)
                .map(|t| t.to);

            // Both states have transitions for this range
            if !(s1_to.is_some() && s2_to.is_some()) {
                return false;
            }

            let s1_to_dsu_class = dsu.find(s1_to.unwrap());
            let s2_to_dsu_class = dsu.find(s2_to.unwrap() + offset);
            if s1_to_dsu_class != s2_to_dsu_class {
                dsu.union(s1_to_dsu_class, s2_to_dsu_class);
                stack.push_front((s1_to.unwrap(), s2_to.unwrap() + offset));
            }
        }
    }

    true
}

pub fn complement(a: Automaton) -> Automaton {
    let mut totalized_states = totalize(a.all_states);

    for state in &mut totalized_states {
        state.accept = !state.accept;
    }

    Automaton {
        name: format!("{}_complement", a.name),
        all_states: totalized_states,
        initial_state: a.initial_state,
    }
}

/// Checks whether automaton `p` is a **syntactic subautomaton** of automaton `q`,
/// taking into account **trigger containment (ranges and ε-transitions)**.
///
/// # Definition
/// `p` is considered a subautomaton of `q` if all structural components of `p`
/// are contained in `q`, with transitions compared using **trigger containment**.
///
/// Formally:
/// - `Q_p ⊆ Q_q` (states)
/// - `F_p ⊆ F_q` (accepting states)
/// - `q0_p = q0_q` (initial state)
/// - For every transition `(s, t, α)` in `p`, there exists a transition
///   `(s, t, β)` in `q` such that `β.contains(α)`
///
/// # Important
/// - This is a **syntactic/structural check**, NOT language inclusion.
/// - ε-transitions are treated explicitly and only match other ε-transitions.
/// - Ranges are compared via interval containment.
///
/// # Returns
/// - `true` if `p` is a subautomaton of `q`
/// - `false` otherwise
pub fn is_subautomaton(p: Automaton, q: Automaton) -> bool {
    // Check if states of p are subset of states of q
    let p_states: HashSet<String> = p.all_states.iter().map(|state| state.id.clone()).collect();
    let q_states: HashSet<String> = q.all_states.iter().map(|state| state.id.clone()).collect();
    if !p_states.is_subset(&q_states) {
        return false;
    }

    // Check if accepting states of p are subset of accepting states of q
    let p_accepting_states: HashSet<String> = p
        .get_accepting_states()
        .iter()
        .map(|state| state.id.clone())
        .collect();
    let q_accepting_states: HashSet<String> = q
        .get_accepting_states()
        .iter()
        .map(|state| state.id.clone())
        .collect();
    println!("{:?}", p);
    println!("{:?}", q);
    if !p_accepting_states.is_subset(&q_accepting_states) {
        return false;
    }

    // Check if initial state of p is equal to the initial state of q
    if p.get_initial_state().id != q.get_initial_state().id {
        return false;
    }

    // Check if transitions of p are subset of transitions of q
    let mut q_index: HashMap<(String, String), Vec<Trigger>> = HashMap::new();
    for (s1, s2, trigger) in &q.get_all_transitions() {
        q_index
            .entry((s1.id.clone(), s2.id.clone()))
            .or_default()
            .push(trigger.clone());
    }

    // For every transition in p, check if it is covered in q
    for (p_s1, p_s2, p_trig) in &p.get_all_transitions() {
        let key = (p_s1.id.clone(), p_s2.id.clone());

        // There must be at least one transition with same (src, dst)
        let Some(q_trigs) = q_index.get(&key) else {
            return false;
        };

        // Check if any trigger in q covers the trigger in p
        let covered = q_trigs.iter().any(|q_trig| q_trig.contains(p_trig));
        if !covered {
            return false;
        }
    }

    true
}
