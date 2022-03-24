; EXPECT: unsat
; EXPECT: ()
(set-option :incremental true)
(set-option :check-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (distinct a b c))
(check-sat-assuming (c))
(get-unsat-assumptions)