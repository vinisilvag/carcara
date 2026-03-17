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
        .filter(|(_, state)| state.accept == true)
        .collect();
    // Has accepting states? If no, the intersection is empty
    if accepting_states.len() == 0 {
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
        let curr_id = *state_map.get(&(s1, s2)).unwrap();

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
        for range in ranges.iter() {
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

    return true;
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

fn reachable_from(a: &Automaton, start: StateId) -> HashSet<StateId> {
    let mut visited = HashSet::new();
    let mut stack = vec![start];

    while let Some(s) = stack.pop() {
        if !visited.insert(s) {
            continue;
        }
        for tr in &a.all_states[s].transitions {
            stack.push(tr.to);
        }
    }

    visited
}

fn can_reach_accept(a: &Automaton, start: StateId) -> bool {
    let reachable = reachable_from(a, start);
    reachable.iter().any(|&q| a.all_states[q].accept)
}

fn possible_cuts(a: &Automaton) -> Vec<StateId> {
    let reachable_init = reachable_from(a, a.initial_state);

    a.all_states
        .iter()
        .enumerate()
        .filter_map(|(id, _)| {
            if reachable_init.contains(&id) && can_reach_accept(a, id) {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

fn sub_automaton(base: &Automaton, from: StateId, to: StateId, name: String) -> Automaton {
    let mut new_states = Vec::new();

    for (i, st) in base.all_states.iter().enumerate() {
        let new_state = State {
            id: st.id.clone(),
            accept: i == to,
            transitions: st.transitions.clone(),
        };
        new_states.push(new_state);
    }

    Automaton {
        name,
        all_states: new_states,
        initial_state: from,
    }
}

// PROTOTIPO
fn backward_concat_xx(a_y: &Automaton) -> Vec<(Automaton, Automaton)> {
    let mut result = Vec::new();

    for q in possible_cuts(a_y) {
        let a1 = sub_automaton(
            a_y,
            a_y.initial_state,
            q,
            format!("{}_prefix_{}", a_y.name, q),
        );

        // um par por estado aceitante final
        for (fid, st) in a_y.all_states.iter().enumerate() {
            if st.accept && can_reach_accept(a_y, q) {
                let a2 = sub_automaton(a_y, q, fid, format!("{}_suffix_{}", a_y.name, fid));
                result.push((a1.clone(), a2));
            }
        }
    }

    result
}

// p is subautomaton of q
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
    if !p_accepting_states.is_subset(&q_accepting_states) {
        return false;
    }

    // Check if initial state of p is equal to the initial state of q
    if p.get_initial_state().id != q.get_initial_state().id {
        return false;
    }

    // Check if transitions of p are subset of transitions of q
    let p_transitions: HashSet<(String, String, Trigger)> = p
        .get_all_transitions()
        .iter()
        .map(|(s1, s2, trigger)| (s1.id.clone(), s2.id.clone(), trigger.clone()))
        .collect();
    let q_transitions: HashSet<(String, String, Trigger)> = q
        .get_all_transitions()
        .iter()
        .map(|(s1, s2, trigger)| (s1.id.clone(), s2.id.clone(), trigger.clone()))
        .collect();
    if !p_transitions.is_subset(&q_transitions) {
        return false;
    }

    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backward_concatenation() {
        let a_y = Automaton::new(
            "a_y",
            "q0",
            vec![("q0", "q1", (98, 98)), ("q1", "q2", (97, 97))],
            vec!["q2"],
        );

        let a_y_det = Automaton::determinize(&a_y);

        println!("{:?}", a_y);
        println!("\n{:?}", a_y_det);

        println!("ans");

        let result = backward_concat_xx(&a_y_det);
        for t in result {
            println!("{:?}", t);
        }
    }

    #[test]
    fn test_automata_intersection() {}

    #[test]
    fn test_equiv_automatas() {
        // <a1> -'a'-> a2 -'a'-> [a3] -'a'-> a4 -'a'-> a5 -'a'-> [a6] -\
        //                                 |                           |
        //                                 \------------'a'------------/
        let a1 = Automaton::new(
            "a1",
            "a1",
            vec![
                ("a1", "a2", (97, 97)),
                ("a2", "a3", (97, 97)),
                ("a3", "a4", (97, 97)),
                ("a4", "a5", (97, 97)),
                ("a5", "a6", (97, 97)),
                ("a6", "a4", (97, 97)),
            ],
            vec!["a3", "a6"],
        );

        // > <b1> -'a'-> b2 -'a'-> [b3] -\
        // |                             |
        // \-------------'a'-------------/
        let a2 = Automaton::new(
            "a2",
            "b1",
            vec![
                ("b1", "b2", (97, 97)),
                ("b2", "b3", (97, 97)),
                ("b3", "b1", (97, 97)),
            ],
            vec!["b3"],
        );

        assert!(is_equivalent(a1, a2));
    }

    #[test]
    fn test_unequiv_automatas() {
        // Language: b*a(a ∪ b)*
        let a1 = Automaton::new(
            "a1",
            "q0",
            vec![
                ("q0", "q1", (97, 97)),
                ("q0", "q0", (98, 98)),
                ("q1", "q1", (97, 97)),
                ("q1", "q1", (98, 98)),
            ],
            vec!["q1"],
        );

        // Language: (a ∪ b)*a(a ∪ b)*
        let a2 = Automaton::new(
            "a2",
            "p0",
            vec![
                ("p0", "p1", (97, 97)),
                ("p0", "p0", (98, 98)),
                ("p1", "p1", (97, 97)),
                ("p1", "p0", (98, 98)),
            ],
            vec!["p1"],
        );

        assert!(!is_equivalent(a1, a2));
    }
}
