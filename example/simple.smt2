(set-logic QF_S)

(declare-const w String)

(assert (str.in_re w (re.+ (str.to_re "a"))))
(assert (or (str.in_re w (re.+ (str.to_re "b")))
            (str.in_re w (re.+ (str.to_re "c")))))

(check-sat)
