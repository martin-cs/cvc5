;; User submitted input from https://github.com/cvc5/cvc5/issues/3696
;; Note this is a particularly weird format with a vast number of exponent bits and very small significand
(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 40))
(declare-fun c () (_ BitVec 6))
(assert (= 0 (fp.to_real (fp a b c))))
(check-sat)

