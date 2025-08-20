use std::collections::{HashMap, HashSet, VecDeque};

use crate::automata::{State, Transition};

use super::{dsu::DSU, utils::intersect_ranges, Automata, StateId};

pub fn intersection(a1: Automata, a2: Automata) {
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

    println!("new states {:?}", new_states);
    println!("state_map {:?}", state_map);

    // Automata {
    //     name: format!("({} intersection {})", a1.name, a2.name),
    //     all_states: new_states,
    //     initial_state: 0,
    // }
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
            let s1_from: Option<StateId> = s1_transitions
                .iter()
                .find(|t| t.range == *range)
                .map(|t| t.to);
            let s2_from: Option<StateId> = s2_transitions
                .iter()
                .find(|t| t.range == *range)
                .map(|t| t.to);

            // Both states have transitions for this range
            if !(s1_from.is_some() && s2_from.is_some()) {
                return false;
            }

            let s1_from_dsu_class = dsu.find(s1_from.unwrap());
            let s2_from_dsu_class = dsu.find(s2_from.unwrap() + offset);
            if s1_from_dsu_class != s2_from_dsu_class {
                dsu.union(s1_from_dsu_class, s2_from_dsu_class);
                stack.push_front((s1_from_dsu_class, s2_from_dsu_class));
            }
        }
    }

    return true;
}
