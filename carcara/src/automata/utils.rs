use crate::automata::TransitionType;

pub fn intersect_ranges(r1: TransitionType, r2: TransitionType) -> Option<(u32, u32)> {
    if let (TransitionType::Range(r1), TransitionType::Range(r2)) = (r1, r2) {
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
