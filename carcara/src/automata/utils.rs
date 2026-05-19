use crate::{
    automata::{State, Transition, Trigger},
    checker::error::CheckerError,
};

pub fn intersect_ranges(r1: Trigger, r2: Trigger) -> Result<Option<(u32, u32)>, CheckerError> {
    match (r1.clone(), r2.clone()) {
        (Trigger::Range(r1), Trigger::Range(r2)) => {
            let start = r1.0.max(r2.0);
            let end = r1.1.min(r2.1);
            if start <= end {
                Ok(Some((start, end)))
            } else {
                Ok(None)
            }
        }
        // TODO: melhorar isso depois
        _ => Err(CheckerError::ExpectedRangesToCalculateTheIntersection(
            r1, r2,
        )),
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

pub fn missing_ranges(
    existing: &[(u32, u32)],
    min_symbol: u32,
    max_symbol: u32,
) -> Vec<(u32, u32)> {
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

pub fn has_overlapping_ranges(ranges: Vec<(u32, u32)>) -> bool {
    if ranges.len() < 2 {
        return false;
    }

    // Sort by the start of the range
    let mut sorted_ranges = ranges.clone();
    sorted_ranges.sort_unstable_by_key(|(start, _)| *start);

    let mut prev_end = sorted_ranges[0].1;
    for &(start, end) in &sorted_ranges[1..] {
        // Intersection
        if start <= prev_end {
            return true;
        }

        // Update the highest end until now
        prev_end = prev_end.max(end);
    }

    false
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

    new_states
}
