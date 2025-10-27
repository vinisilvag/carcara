use crate::automata::Trigger;

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
