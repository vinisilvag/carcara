(set-logic QF_S)

(declare-const z String)
(declare-const u String)
(declare-const y String)
(declare-const x String)

(assert (= y (str.++ z u)))
(assert (= y (str.++ x x)))
(assert (str.in_re z (str.to_re "b")))
(assert (str.in_re u (str.to_re "a")))

(check-sat)
