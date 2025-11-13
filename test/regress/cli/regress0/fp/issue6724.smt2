;; User submitted input from https://github.com/cvc5/cvc5/issues/6724
;; Note this is a particularly weird format with a vast number of exponent bits and very small significand
(declare-fun A () (Array Float32 Float64))
(declare-fun A2 () (Array Float32 Float64))
(assert (and (distinct A A2) (= (_ NaN 11 53) (select A2 (_ -oo 8 24)))))
(check-sat)

