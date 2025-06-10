pub fn intersect_ranges(r1: (u32, u32), r2: (u32, u32)) -> Option<(u32, u32)> {
    let start = r1.0.max(r2.0);
    let end = r1.1.min(r2.1);
    if start <= end {
        Some((start, end))
    } else {
        None
    }
}
