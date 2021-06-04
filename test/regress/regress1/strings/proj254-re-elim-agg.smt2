(set-logic ALL)
(set-info :status sat)
(set-option :produce-models true)
(set-option :strings-exp true)
(set-option :re-elim true)
(set-option :re-elim-agg true)
(declare-fun a () String)
(assert (str.in_re a (re.++ (re.+ (str.to_re "AB")) (str.to_re "B"))))
(assert (<= (str.len a) 4))
(check-sat)