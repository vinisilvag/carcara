use std::collections::{HashMap, HashSet, VecDeque};

use crate::automata::{State, Transition};

use super::{dsu::DSU, utils::intersect_ranges, Automata, StateId};

// TODO: do not clone the graph every recursion step
pub fn recursive_dfs(graph: Vec<Vec<StateId>>, visited: &mut Vec<bool>, state: StateId) {
    visited[state] = true;
    for edge in graph[state].clone() {
        if !visited[edge] {
            recursive_dfs(graph.clone(), visited, edge);
        }
    }
}

pub fn has_reachable_accepting_state(a: Automata) -> bool {
    let accepting_states: Vec<_> = a
        .all_states
        .iter()
        .enumerate()
        .filter(|(index, state)| state.accept == true)
        .collect();
    // Has accepting states? If no, the intersection is empty
    if accepting_states.len() == 0 {
        return false;
    }

    // Creating an adjacency list based on the automata structure
    let mut graph: Vec<Vec<StateId>> = vec![Vec::new(); a.all_states.len()];
    for (state_id, state) in a.all_states.iter().enumerate() {
        for transition in &state.transitions {
            if transition.to == state_id {
                continue;
            }
            graph[state_id].push(transition.to);
        }
    }

    // Checking reachability with DFS
    let mut visited: Vec<bool> = vec![false; a.all_states.len()];
    recursive_dfs(graph, &mut visited, a.initial_state);
    for (state_id, state) in accepting_states {
        if visited[state_id] {
            return true;
        }
    }

    false
}

pub fn intersection(a1: Automata, a2: Automata) -> Automata {
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
                if let Some(range) = intersect_ranges(t1.range, t2.range) {
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
                        .insert(Transition::new(next_id, range));
                }
            }
        }
    }

    Automata {
        name: format!("({} ∩ {})", a1.name, a2.name),
        all_states: new_states,
        initial_state: 0,
    }
}

// Implementation of automata equivalence checking based on the Hopcroft-Karp algorithm,
// adapted for testing the equivalence of deterministic finite automata (DFAs), as described
// in the paper "A Linear Algorithm for Testing Equivalence of Finite Automata".
pub fn is_equivalent(a1: Automata, a2: Automata) -> bool {
    let offset = a1.all_states.len();

    // Work with StateId's
    let states: Vec<StateId> = (0..(a1.all_states.len() + a2.all_states.len())).collect();

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
                .map(|t| t.range)
                .chain(s2_transitions.iter().map(|t| t.range))
                .collect::<Vec<_>>(),
        );
        for range in ranges.iter() {
            let s1_to: Option<StateId> = s1_transitions
                .iter()
                .find(|t| t.range == *range)
                .map(|t| t.to);
            let s2_to: Option<StateId> = s2_transitions
                .iter()
                .find(|t| t.range == *range)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_automata_intersection() {}

    #[test]
    fn test_equiv_automatas() {
        // <a1> -'a'-> a2 -'a'-> [a3] -'a'-> a4 -'a'-> a5 -'a'-> [a6] -\
        //                                 |                           |
        //                                 \------------'a'------------/
        let a1 = Automata::new(
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
        let a2 = Automata::new(
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
        let a1 = Automata::new(
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
        let a2 = Automata::new(
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
