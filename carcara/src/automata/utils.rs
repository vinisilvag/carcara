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

    return new_states;
}

#[cfg(test)]
mod tests {
    use super::*;

    // Auxiliar functions
    fn range_to_sink(state: &State, sink_id: usize) -> Vec<(u32, u32)> {
        state
            .transitions
            .iter()
            .filter_map(|t| {
                if t.to == sink_id {
                    if let Trigger::Range(r) = t.trigger {
                        Some(r)
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect()
    }

    fn all_ranges(state: &State) -> Vec<(u32, u32)> {
        state
            .transitions
            .iter()
            .filter_map(|t| {
                if let Trigger::Range(r) = t.trigger {
                    Some(r)
                } else {
                    None
                }
            })
            .collect()
    }

    // Intersect ranges
    #[test]
    fn test_intersection_simple_overlap() {
        let r1 = Trigger::Range((0, 10));
        let r2 = Trigger::Range((5, 15));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), Some((5, 10)));
    }

    #[test]
    fn test_intersection_identical_ranges() {
        let r1 = Trigger::Range((3, 7));
        let r2 = Trigger::Range((3, 7));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), Some((3, 7)));
    }

    #[test]
    fn test_intersection_contained_range() {
        let r1 = Trigger::Range((0, 10));
        let r2 = Trigger::Range((3, 5));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), Some((3, 5)));
    }

    #[test]
    fn test_intersection_touching_ranges() {
        // Closed intervals: [0,5] ∩ [5,10] = [5,5]
        let r1 = Trigger::Range((0, 5));
        let r2 = Trigger::Range((5, 10));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), Some((5, 5)));
    }

    #[test]
    fn test_intersection_no_overlap() {
        let r1 = Trigger::Range((0, 4));
        let r2 = Trigger::Range((5, 10));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), None);
    }

    #[test]
    fn test_intersection_unsorted_inputs() {
        // Order of r1 and r2 should not matter
        let r1 = Trigger::Range((8, 12));
        let r2 = Trigger::Range((3, 10));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), Some((8, 10)));
    }

    #[test]
    fn test_intersection_single_point_overlap() {
        let r1 = Trigger::Range((5, 5));
        let r2 = Trigger::Range((5, 5));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), Some((5, 5)));
    }

    #[test]
    fn test_intersection_empty_unsorted_inputs() {
        let r1 = Trigger::Range((10, 20));
        let r2 = Trigger::Range((0, 9));
        assert_eq!(intersect_ranges(r1, r2).unwrap(), None);
    }

    #[test]
    fn intersection_non_range_trigger_panics() {
        let r1 = Trigger::Range((0, 10));
        let r2 = Trigger::Epsilon;
        assert!(intersect_ranges(r1, r2).is_err());
    }

    // Normalize ranges
    #[test]
    fn test_normalize_empty() {
        let ranges: Vec<(u32, u32)> = vec![];
        let normalized = normalize_ranges(ranges);
        assert!(normalized.is_empty());
    }

    #[test]
    fn test_normalize_single_range() {
        let ranges = vec![(3, 7)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(3, 7)]);
    }

    #[test]
    fn test_normalize_already_normalized() {
        let ranges = vec![(0, 3), (5, 8), (10, 15)];
        let normalized = normalize_ranges(ranges.clone());
        assert_eq!(normalized, ranges);
    }

    #[test]
    fn test_normalize_overlapping_ranges() {
        let ranges = vec![(0, 5), (3, 10)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 10)]);
    }

    #[test]
    fn test_normalize_adjacent_ranges() {
        // adjacency: [0,3] and [4,7]
        let ranges = vec![(0, 3), (4, 7)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 7)]);
    }

    #[test]
    fn test_normalize_unsorted_ranges() {
        let ranges = vec![(10, 12), (0, 3), (5, 8)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 3), (5, 8), (10, 12)]);
    }

    #[test]
    fn test_normalize_unsorted_overlapping_and_adjacent() {
        let ranges = vec![(5, 8), (1, 3), (2, 6), (9, 10)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(1, 10)]);
    }

    #[test]
    fn test_normalize_nested_ranges() {
        let ranges = vec![(0, 20), (5, 10), (12, 18)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 20)]);
    }

    #[test]
    fn test_normalize_degenerate_ranges() {
        let ranges = vec![(5, 5), (6, 6), (8, 8)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(5, 6), (8, 8)]);
    }

    #[test]
    fn test_normalize_large_gap() {
        let ranges = vec![(0, 1), (10, 11)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 1), (10, 11)]);
    }

    #[test]
    fn test_normalize_multiple_chain() {
        let ranges = vec![(0, 2), (3, 5), (6, 8)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 8)]);
    }

    #[test]
    fn test_normalize_same_start_different_ends() {
        let ranges = vec![(0, 3), (0, 10), (0, 5)];
        let normalized = normalize_ranges(ranges);
        assert_eq!(normalized, vec![(0, 10)]);
    }

    // List missing ranges
    #[test]
    fn test_missing_on_empty_ranges() {
        let existing: Vec<(u32, u32)> = vec![];
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(0, 10)]);
    }

    #[test]
    fn test_missing_single_range_exact_cover() {
        let existing = vec![(0, 10)];
        let holes = missing_ranges(&existing, 0, 10);
        assert!(holes.is_empty());
    }

    #[test]
    fn test_missing_single_range_inside_bounds() {
        let existing = vec![(3, 7)];
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(0, 2), (8, 10)]);
    }

    #[test]
    fn test_missing_ranges_gap_in_middle() {
        let existing = vec![(0, 3), (7, 10)];
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(4, 6)]);
    }

    #[test]
    fn test_missing_ranges_multiple_gaps() {
        let existing = vec![(1, 2), (5, 6), (9, 10)];
        let holes = missing_ranges(&existing, 0, 12);
        assert_eq!(holes, vec![(0, 0), (3, 4), (7, 8), (11, 12)]);
    }

    #[test]
    fn test_missing_ranges_unsorted_and_overlapping_existing() {
        let existing = vec![(5, 8), (1, 3), (2, 6)];
        // normalize_ranges -> [(1, 8)]
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(0, 0), (9, 10)]);
    }

    #[test]
    fn test_missing_adjacent_ranges_no_gap() {
        let existing = vec![(0, 3), (4, 6), (7, 10)];
        let holes = missing_ranges(&existing, 0, 10);
        assert!(holes.is_empty());
    }

    #[test]
    fn test_missing_range_starts_after_min() {
        let existing = vec![(5, 10)];
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(0, 4)]);
    }

    #[test]
    fn test_missing_range_ends_before_max() {
        let existing = vec![(0, 5)];
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(6, 10)]);
    }

    #[test]
    fn test_missing_degenerate_ranges() {
        let existing = vec![(2, 2), (4, 4)];
        let holes = missing_ranges(&existing, 0, 5);
        assert_eq!(holes, vec![(0, 1), (3, 3), (5, 5)]);
    }

    #[test]
    fn test_missing_single_point_domain_uncovered() {
        let existing: Vec<(u32, u32)> = vec![];
        let holes = missing_ranges(&existing, 5, 5);
        assert_eq!(holes, vec![(5, 5)]);
    }

    #[test]
    fn test_missing_single_point_domain_covered() {
        let existing = vec![(5, 5)];
        let holes = missing_ranges(&existing, 5, 5);
        assert!(holes.is_empty());
    }

    #[test]
    fn test_missing_after_merging_chain() {
        let existing = vec![(1, 2), (3, 4), (6, 7)];
        // normalize -> [(1,4), (6,7)]
        let holes = missing_ranges(&existing, 0, 10);
        assert_eq!(holes, vec![(0, 0), (5, 5), (8, 10)]);
    }

    // Overlapping function
    #[test]
    fn test_overlapping_empty_vector() {
        let ranges = vec![];
        assert!(!has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_overlapping_single_range() {
        let ranges = vec![(0, 10)];
        assert!(!has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_non_overlapping_ranges() {
        let ranges = vec![(0, 5), (6, 10), (11, 20)];
        assert!(!has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_simple_overlap() {
        let ranges = vec![(0, 5), (4, 10)];
        assert!(has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_touching_ranges_are_overlapping() {
        // Because the ranges are closed: [0,5] and [5,10]
        let ranges = vec![(0, 5), (5, 10)];
        assert!(has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_overlapping_unsorted_input() {
        let ranges = vec![(10, 20), (0, 5), (4, 8)];
        assert!(has_overlapping_ranges(ranges));
    }

    #[test]
    fn test_overlapping_nested_ranges() {
        let ranges = vec![(0, 20), (5, 10), (21, 30)];
        assert!(has_overlapping_ranges(ranges));
    }

    // Totalize ranges
    #[test]
    fn test_totalize_adds_sink_state() {
        let s0 = State::new("q0", false);
        let states = vec![s0];

        let totalized = totalize(states);

        assert_eq!(totalized.len(), 2);

        let sink = &totalized[1];
        assert_eq!(sink.id, "sink");
        assert!(!sink.accept);
    }

    #[test]
    fn test_sink_has_self_loop_over_full_alphabet() {
        let s0 = State::new("q0", false);
        let totalized = totalize(vec![s0]);

        let sink = &totalized[1];
        let ranges = all_ranges(sink);

        assert!(missing_ranges(&ranges, 0, 255).is_empty());
    }

    #[test]
    fn test_state_with_full_coverage_gets_no_sink_transitions() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 255))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        assert!(sink_ranges.is_empty());
    }

    #[test]
    fn test_state_with_missing_ranges_gets_sink_transitions() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 9))));
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((20, 29))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        let mut sorted_ranges = sink_ranges.clone();
        sorted_ranges.sort_unstable_by_key(|(start, _)| *start);

        assert_eq!(sorted_ranges, vec![(10, 19), (30, 255)]);
    }

    #[test]
    fn test_overlapping_ranges_are_normalized_before_totalizing() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 10))));
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((5, 20))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        assert_eq!(sink_ranges, vec![(21, 255)]);
    }

    #[test]
    fn test_adjacent_ranges_are_merged_before_holes() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 9))));
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((10, 19))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let sink_ranges = range_to_sink(q0, 1);
        assert_eq!(sink_ranges, vec![(20, 255)]);
    }

    #[test]
    fn test_totalized_state_covers_entire_alphabet() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((10, 20))));

        let totalized = totalize(vec![s0]);
        let q0 = &totalized[0];

        let mut all = all_ranges(q0);
        all.sort();

        let normalized = normalize_ranges(all);
        assert_eq!(normalized, vec![(0, 255)]);
    }

    #[test]
    fn test_multiple_states_all_get_totalized() {
        let mut s0 = State::new("q0", false);
        s0.transitions
            .insert(Transition::new(0, Trigger::Range((0, 10))));

        let mut s1 = State::new("q1", true);
        s1.transitions
            .insert(Transition::new(1, Trigger::Range((20, 30))));

        let totalized = totalize(vec![s0, s1]);

        let sink_id = 2;

        let sink_ranges_q0 = range_to_sink(&totalized[0], sink_id);
        let sink_ranges_q1 = range_to_sink(&totalized[1], sink_id);

        assert!(!sink_ranges_q0.is_empty());
        assert!(!sink_ranges_q1.is_empty());
    }
}
