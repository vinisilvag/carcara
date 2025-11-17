use crate::automata::{State, Transition, Trigger};

pub fn intersect_ranges(r1: Trigger, r2: Trigger) -> Option<(u32, u32)> {
    if let (Trigger::Range(r1), Trigger::Range(r2)) = (r1, r2) {
        let start = r1.0.max(r2.0);
        let end = r1.1.min(r2.1);
        if start <= end {
            Some((start, end))
        } else {
            None
        }
    } else {
        unreachable!("should be only dfas and not nfas");
    }
}

fn normalize_ranges(mut ranges: Vec<(u32, u32)>) -> Vec<(u32, u32)> {
    if ranges.is_empty() {
        return ranges;
    }

    ranges.sort_by(|a, b| a.0.cmp(&b.0));

    let mut result = vec![ranges[0]];

    for (l, r) in ranges.into_iter().skip(1) {
        let last = result.last_mut().unwrap();
        if l <= last.1 + 1 {
            last.1 = last.1.max(r);
        } else {
            result.push((l, r));
        }
    }
    result
}

fn missing_ranges(existing: &[(u32, u32)], min_symbol: u32, max_symbol: u32) -> Vec<(u32, u32)> {
    let normalized = normalize_ranges(existing.to_vec());
    let mut holes = Vec::new();

    let mut cursor = min_symbol;

    for (l, r) in normalized {
        if cursor < l {
            holes.push((cursor, l - 1));
        }
        cursor = r + 1;
    }

    if cursor <= max_symbol {
        holes.push((cursor, max_symbol));
    }

    holes
}

pub fn totalize(states: Vec<State>) -> Vec<State> {
    let mut new_states = states.clone();

    let sink_id = states.len();
    let mut sink_state = State::new("sink", false);
    sink_state
        .transitions
        .insert(Transition::new(sink_id, Trigger::Range((0, 255))));
    new_states.push(sink_state);

    for state in &mut new_states[..sink_id] {
        let mut existing_ranges = Vec::new();
        for t in &state.transitions {
            if let Trigger::Range((l, r)) = t.trigger {
                existing_ranges.push((l, r));
            }
        }

        let holes = missing_ranges(&existing_ranges, 0, 255);

        for (l, r) in holes {
            state
                .transitions
                .insert(Transition::new(sink_id, Trigger::Range((l, r))));
        }
    }

    return new_states;
}
