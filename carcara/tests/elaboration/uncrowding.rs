#[test]
fn uncrowd() {
    test_cases! {
        pipeline = Uncrowd,
        problem =  "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)
        ",
        "Simple crowding literal" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not a) b) :rule hole)
            (step t3 (cl b) :rule resolution :premises (t1 t2) :args (a true))"
            ->
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not a) b) :rule hole)
            (step t3.t1 (cl b b) :rule resolution :premises (t1 t2) :args (a true))
            (step t3 (cl b) :rule contraction :premises (t3.t1))",
        }
        "No crowding literals" {
            "(step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y) :rule hole)
            (step t3 (cl a b y) :rule resolution :premises (t1 t2) :args (x true))"
            ->
            "(step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y) :rule hole)
            (step t3 (cl a b y) :rule resolution :premises (t1 t2) :args (x true))",
        }
        "Multiple contractions" {
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not a) b c) :rule hole)
            (step t3 (cl (not b) c) :rule hole)
            (step t4 (cl c) :rule resolution :premises (t1 t2 t3) :args (a true b true))"
            ->
            "(step t1 (cl a b) :rule hole)
            (step t2 (cl (not a) b c) :rule hole)
            (step t3 (cl (not b) c) :rule hole)
            (step t4.t1 (cl b b c) :rule resolution :premises (t1 t2) :args (a true))
            (step t4.t2 (cl b c) :rule contraction :premises (t4.t1))
            (step t4.t3 (cl c c) :rule resolution :premises (t4.t2 t3) :args (b true))
            (step t4 (cl c) :rule contraction :premises (t4.t3))",
        }
    }
}

#[test]
fn uncrowd_with_rotation() {
    test_cases! {
        pipeline = Uncrowd,
        uncrowd_rotate = true,
        problem =  "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (declare-const w Bool)
            (declare-const x Bool)
            (declare-const y Bool)
            (declare-const z Bool)",
        "Crowding literals, with premise rotation" {
            "(step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y a c) :rule hole)
            (step t3 (cl (not y) z b) :rule hole)
            (step t4 (cl (not a)) :rule hole)
            (step t5 (cl (not z) c) :rule hole)
            (step t6 (cl d (not b) w) :rule hole)
            (step t7 (cl d (not c)) :rule hole)
            (step t8 (cl (not d)) :rule hole)
            (step t9 (cl w)
                :rule resolution
                :premises (t1 t2 t3 t4 t5 t6 t7 t8)
                :args (x true y true a true z true b true c true d true))"
            ->
            "(step t1 (cl x a b) :rule hole)
            (step t2 (cl (not x) y a c) :rule hole)
            (step t3 (cl (not y) z b) :rule hole)
            (step t4 (cl (not a)) :rule hole)
            (step t5 (cl (not z) c) :rule hole)
            (step t6 (cl d (not b) w) :rule hole)
            (step t7 (cl d (not c)) :rule hole)
            (step t8 (cl (not d)) :rule hole)
            (step t9.t1 (cl a b a c z b) :rule resolution :premises (t1 t2 t3)
                :args (x true y true))
            (step t9.t2 (cl a b c z) :rule contraction :premises (t9.t1))
            (step t9.t3 (cl c c d w) :rule resolution :premises (t9.t2 t4 t5 t6)
                :args (a true z true b true))
            (step t9.t4 (cl c d w) :rule contraction :premises (t9.t3))
            (step t9.t5 (cl d w d) :rule resolution :premises (t9.t4 t7) :args (c true))
            (step t9.t6 (cl d w) :rule contraction :premises (t9.t5))
            (step t9 (cl w) :rule resolution :premises (t9.t6 t8) :args (d true))",
        }
    }
}
