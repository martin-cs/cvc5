; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (= (+ (+ (+ (* 6 x0) (* 2 x1)) (* 22 x2)) (* (- 18) x3)) (- 15)))
(assert (let ((_let_1 (- 25))) (> (+ (+ (+ (* (- 8) x0) (* _let_1 x1)) (* _let_1 x2)) (* 7 x3)) 10)))
(assert (< (+ (+ (+ (* 8 x0) (* 25 x1)) (* (- 7) x2)) (* (- 29) x3)) (- 25)))
(assert (<= (+ (+ (+ (* 27 x0) (* 17 x1)) (* (- 24) x2)) (* (- 5) x3)) 13))
(assert (< (+ (+ (+ (* 5 x0) (* (- 3) x1)) (* 0 x2)) (* 4 x3)) (- 26)))
(assert (< (+ (+ (+ (* 25 x0) (* 7 x1)) (* 27 x2)) (* (- 14) x3)) 30))
(assert (< (+ (+ (+ (* (- 22) x0) (* (- 17) x1)) (* 9 x2)) (* (- 20) x3)) (- 19)))
(assert (>= (+ (+ (+ (* 31 x0) (* (- 16) x1)) (* 0 x2)) (* 6 x3)) 18))
(check-sat)