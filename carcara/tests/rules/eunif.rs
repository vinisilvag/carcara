#[test]
fn g_eunif() {
    test_cases! {
        definitions = "
            (declare-sort T 0)
            (declare-fun a () T)
            (declare-fun b () T)
            (declare-fun c () T)
            (declare-fun d () T)
            (declare-fun e () T)
            (declare-fun f (T) T)
            (declare-fun g (T) T)
            (declare-fun h (T T) T)
            (declare-fun p (T) Bool)
        ",
        "Direct premise and symmetry" {
            "(assume h1 (= a b))
            (step t2 (cl (= a b)) :rule g_eunif :premises (h1))": true,

            "(assume h1 (= a b))
            (step t2 (cl (= b a)) :rule g_eunif :premises (h1))": true,
        }
        "Transitivity" {
            "(assume h1 (= a b)) (assume h2 (= b c))
            (step t3 (cl (= a c)) :rule g_eunif :premises (h1 h2))": true,

            "(assume h1 (= b a)) (assume h2 (= c b)) (assume h3 (= c d))
            (step t4 (cl (= a d)) :rule g_eunif :premises (h1 h2 h3))": true,

            "(assume h1 (= c d)) (assume h2 (= a b)) (assume h3 (= b c))
            (step t4 (cl (= d a)) :rule g_eunif :premises (h1 h2 h3))": true,
        }
        "Congruence" {
            "(assume h1 (= a b))
            (step t2 (cl (= (f a) (f b))) :rule g_eunif :premises (h1))": true,

            "(assume h1 (= a b))
            (step t2 (cl (= (h (g a) c) (h (g b) c))) :rule g_eunif :premises (h1))": true,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (h a c) (h b d))) :rule g_eunif :premises (h1 h2))": true,

            "(assume h1 (= a b))
            (step t2 (cl (= (p a) (p b))) :rule g_eunif :premises (h1))": true,

            "(assume h1 (= a b))
            (step t2 (cl (= (f (f a)) (f (f b)))) :rule g_eunif :premises (h1))": true,
        }
        "Congruence and transitivity combined" {
            "(assume h1 (= a b)) (assume h2 (= (f b) c)) (assume h3 (= c d))
            (step t4 (cl (= (f a) d)) :rule g_eunif :premises (h1 h2 h3))": true,

            "(assume h1 (= a b)) (assume h2 (= b c))
            (step t3 (cl (= (f a) (f c))) :rule g_eunif :premises (h1 h2))": true,

            "(assume h1 (= a b)) (assume h2 (= (h a a) c)) (assume h3 (= (h b b) d))
            (step t4 (cl (= c d)) :rule g_eunif :premises (h1 h2 h3))": true,
        }
        "Reflexivity, with no premises" {
            "(step t1 (cl (= a a)) :rule g_eunif)": true,

            "(step t1 (cl (= (f a) (f a))) :rule g_eunif)": true,
        }
        "Unused premises are allowed" {
            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= a b)) :rule g_eunif :premises (h1 h2))": true,
        }
        "Multiple steps in the same proof" {
            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= (f a) (f b))) :rule g_eunif :premises (h1))
            (step t4 (cl (= (h c a) (h d a))) :rule g_eunif :premises (h2))": true,

            // The second step must not see the equalities of the first step's premises
            "(assume h1 (= a b))
            (step t2 (cl (= (f a) (f b))) :rule g_eunif :premises (h1))
            (step t3 (cl (= a b)) :rule g_eunif)": false,
        }
        "Conclusion is not entailed" {
            "(assume h1 (= a b))
            (step t2 (cl (= a c)) :rule g_eunif :premises (h1))": false,

            "(assume h1 (= a b)) (assume h2 (= c d))
            (step t3 (cl (= a d)) :rule g_eunif :premises (h1 h2))": false,

            // Congruence is not injectivity
            "(assume h1 (= (f a) (f b)))
            (step t2 (cl (= a b)) :rule g_eunif :premises (h1))": false,

            "(assume h1 (= a b))
            (step t2 (cl (= (f a) (g b))) :rule g_eunif :premises (h1))": false,

            "(step t1 (cl (= a b)) :rule g_eunif)": false,
        }
        "Conjunction premises" {
            "(assume h1 (and (= a b) (= c d)))
            (step t2 (cl (= (h a c) (h b d))) :rule g_eunif :premises (h1))": true,

            "(assume h1 (and (= a b) (= b c)))
            (step t2 (cl (= (f a) (f c))) :rule g_eunif :premises (h1))": true,

            "(assume h1 (and (= a b) (= c d))) (assume h2 (= (f b) c))
            (step t3 (cl (= (f a) d)) :rule g_eunif :premises (h1 h2))": true,

            // Conjuncts are not implicitly usable if the premise is not given
            "(assume h1 (and (= a b) (= b c))) (assume h2 (= c d))
            (step t3 (cl (= a d)) :rule g_eunif :premises (h2))": false,
        }
        "Conjunction premise with non-equality conjunct" {
            "(assume h1 (and (= a b) (p a)))
            (step t2 (cl (= a b)) :rule g_eunif :premises (h1))": false,

            "(assume h1 (and (= a b) (and (= b c) (= c d))))
            (step t2 (cl (= a b)) :rule g_eunif :premises (h1))": false,
        }
        "Premise is not an equality" {
            "(assume h1 (not (= a b)))
            (step t2 (cl (= a b)) :rule g_eunif :premises (h1))": false,

            "(assume h1 (p a))
            (step t2 (cl (= a a)) :rule g_eunif :premises (h1))": false,
        }
        "Conclusion clause is of the wrong form" {
            "(assume h1 (= a b))
            (step t2 (cl (not (= a b))) :rule g_eunif :premises (h1))": false,

            "(assume h1 (= a b))
            (step t2 (cl (= a b) (= b a)) :rule g_eunif :premises (h1))": false,
        }
    }
}
