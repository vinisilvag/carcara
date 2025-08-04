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

pub fn is_equivalent(a1: Automata, a2: Automata) -> bool {
    let states = HashSet::new();
    let transitions = HashSet::new();
    let accepting_states = HashSet::new();

    let mut stack = VecDeque::new();
    // stack.push_front();

    while let Some((s1, s2)) = stack.pop_front() {
        if accepting_states.contains(s1) != accepting_states.contains(s2) {
            return false;
        }

        //
    }

    return true;
}
