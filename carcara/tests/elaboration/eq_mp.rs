#[test]
fn eq_mp() {
    test_cases! {
        pipeline = Local,
        problem =  "
            (declare-const p Bool)
            (declare-const q Bool)
        ",
        "Standard case" {
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3 (cl q) :rule eq_mp :premises (h1 h2))"
            ->
            "(assume h1 p)
            (assume h2 (= p q))
            (step t3.t1 (cl (not (= p q)) (not p) q) :rule equiv_pos2)
            (step t3 (cl q) :rule resolution :premises (t3.t1 h2 h1) :args ((= p q) false p false))",
        }
        "Conclusion is the negation of the first premise" {
            "(assume h1 p)
            (assume h2 (= p (not p)))
            (step t3 (cl (not p)) :rule eq_mp :premises (h1 h2))"
            ->
            "(assume h1 p)
            (assume h2 (= p (not p)))
            (step t3.t1.t1 (cl (not (= p (not p))) (not p) (not p)) :rule equiv_pos2)
            (step t3 (cl (not p)) :rule resolution :premises (t3.t1.t1 h2)
                :args ((= p (not p)) false))",
        }
    }
}
