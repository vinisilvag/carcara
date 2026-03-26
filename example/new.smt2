(set-logic QF_S)

(set-info :status unsat)

(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

(assert (= a (str.++ b c)))
(assert (= b (str.++ d c)))

(assert (str.in_re a (re.+ (str.to_re "y"))))
(assert (str.in_re c (re.+ (str.to_re "x"))))

(check-sat)
(get-model)
