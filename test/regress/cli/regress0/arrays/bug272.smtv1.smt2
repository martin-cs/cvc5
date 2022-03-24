(set-option :incremental false)
(set-info :status sat)
(set-logic QF_AUF)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun v0 () (Array Index Element))
(declare-fun v1 () Index)
(declare-fun v2 () Index)
(declare-fun v3 () Element)
(check-sat-assuming ( (let ((_let_0 (store (store v0 v1 v3) v2 v3))) (let ((_let_1 (distinct _let_0 _let_0))) (let ((_let_2 (distinct v3 (select v0 v2)))) (let ((_let_3 (ite _let_2 _let_0 (store _let_0 v1 (select v0 v2))))) (let ((_let_4 (ite (distinct v2 v2) (ite (= v1 v2) (store v0 v1 v3) (store _let_0 v1 (select v0 v2))) _let_0))) (let ((_let_5 (ite (distinct v0 _let_0) v0 (ite (distinct (select _let_0 v1) v3) (store (store v0 v1 v3) v2 (select v0 v2)) (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) _let_0 (store (store v0 v1 v3) v2 (select v0 v2))))))) (let ((_let_6 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) _let_3 (store _let_0 v1 (select v0 v2))))) (let ((_let_7 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (store v0 v1 v3) _let_3))) (let ((_let_8 (ite (distinct v2 v2) (store (store v0 v1 v3) v2 (select v0 v2)) _let_5))) (let ((_let_9 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v0 _let_0))) (let ((_let_10 (ite (distinct (store _let_0 v1 (select v0 v2)) _let_0) _let_9 (ite (distinct (select _let_0 v1) v3) _let_7 _let_4)))) (let ((_let_11 (ite (distinct v2 v2) _let_4 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) _let_0 (store (store v0 v1 v3) v2 (select v0 v2)))))) (let ((_let_12 (ite _let_1 _let_5 _let_3))) (let ((_let_13 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) v1 v1))) (let ((_let_14 (ite (distinct (store _let_0 v1 (select v0 v2)) _let_0) (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v1 v1) (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v1 v1)))) (let ((_let_15 (ite _let_2 _let_13 _let_14))) (let ((_let_16 (ite (= v1 v2) v2 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v1 v1)))) (let ((_let_17 (ite (distinct (store _let_0 v1 (select v0 v2)) _let_0) _let_14 _let_15))) (let ((_let_18 (ite (distinct v2 v2) _let_15 v1))) (let ((_let_19 (ite (distinct v2 v2) (ite (distinct v0 _let_0) v2 v2) (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) (ite (= v1 v2) _let_13 v2) _let_17)))) (let ((_let_20 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_18 v2))) (let ((_let_21 (ite _let_1 (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_15) v2))) (let ((_let_22 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) _let_20 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) (ite (= v1 v2) _let_13 v2) _let_17)))) (let ((_let_23 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) _let_14 (ite (distinct (select _let_0 v1) v3) (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (distinct v0 _let_0) v2 v2))))) (let ((_let_24 (ite (distinct v2 v2) v3 v3))) (let ((_let_25 (ite (distinct (select _let_0 v1) v3) v3 (select _let_0 v1)))) (let ((_let_26 (ite _let_2 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)) (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2))))) (let ((_let_27 (ite (distinct (store _let_0 v1 (select v0 v2)) _let_0) _let_25 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)) _let_24)))) (let ((_let_28 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) (select v0 v2) (select _let_0 v1)))) (let ((_let_29 (ite (distinct (store _let_0 v1 (select v0 v2)) _let_0) _let_24 _let_25))) (let ((_let_30 (ite (= v1 v2) _let_25 _let_28))) (let ((_let_31 (ite _let_1 _let_27 (select _let_0 v1)))) (let ((_let_32 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) _let_25 _let_27))) (let ((_let_33 (ite _let_1 _let_24 _let_25))) (let ((_let_34 (ite (distinct v0 _let_0) (select v0 v2) _let_26))) (let ((_let_35 (store _let_9 (ite _let_1 v1 (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_15)) (ite _let_1 v3 (ite (distinct v2 v2) _let_24 _let_25))))) (let ((_let_36 (select _let_7 (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13)))) (let ((_let_37 (store (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) _let_0 (ite (distinct (select _let_0 v1) v3) _let_7 _let_4)) (ite (distinct v0 _let_0) v2 v2) (select v0 v2)))) (let ((_let_38 (store _let_4 _let_22 (select _let_12 _let_22)))) (let ((_let_39 (= _let_6 _let_38))) (let ((_let_40 (=> (distinct _let_26 _let_36) (distinct _let_11 _let_4)))) (let ((_let_41 (or (=> (distinct (select v0 v2) _let_24) (= (distinct (store _let_4 _let_14 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)))) (store _let_4 _let_14 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2))))) (= _let_6 (ite (= v1 v2) (store v0 v1 v3) (store _let_0 v1 (select v0 v2)))))) (=> (= v1 v2) (= _let_12 _let_12))))) (ite (or (or (= v2 (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_15)) (ite (xor _let_40 _let_40) (=> (distinct v2 v2) (distinct v2 v2)) (or (not (distinct _let_3 _let_8)) (distinct _let_10 _let_6)))) (xor (= (and (or (xor (not (not (distinct (select _let_0 v1) v3))) (ite (= (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v1 v1)) (not (not (or (= (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) _let_0 (ite (distinct (select _let_0 v1) v3) _let_7 _let_4)) (store _let_4 _let_14 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2))))) (= (select _let_12 _let_22) _let_28)))) (distinct (store _let_0 v1 (select v0 v2)) _let_0))) (distinct _let_37 (ite (distinct (select _let_0 v1) v3) _let_7 _let_4))) (not (= (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) (ite (= v1 v2) _let_13 v2) _let_17) _let_13))) (and (not (= v3 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)))) (not (or (and (or (= (ite (distinct (select _let_0 v1) v3) _let_7 _let_4) _let_11) (distinct (select _let_0 v1) (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2))))) (not (= _let_33 _let_34))) (and (xor (=> (= (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)) _let_26) _let_39) (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2)))) (or (= _let_0 _let_0) (distinct _let_21 _let_15))))))) (distinct (store (store v0 v1 v3) v2 (select v0 v2)) (store v0 v1 v3)))) (xor (ite (=> (distinct (ite (= v1 v2) (store v0 v1 v3) (store _let_0 v1 (select v0 v2))) _let_5) (=> (distinct _let_8 (store v0 v1 v3)) (not (xor (and (= (= (distinct v0 _let_0) (= (select _let_0 v1) _let_28)) (= (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (= v1 v2) _let_13 v2))) (=> (= (distinct (store (store _let_4 _let_14 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)))) _let_18 (select v0 v2)) (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) _let_0 (store (store v0 v1 v3) v2 (select v0 v2)))) (distinct (select v0 v2) _let_29)) (distinct v2 v2))) (distinct (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v1 v1) _let_19))))) (=> _let_2 (or (distinct _let_12 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) _let_0 (ite (distinct (select _let_0 v1) v3) _let_7 _let_4))) (or (= _let_34 _let_26) (= (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (distinct v0 _let_0) v2 v2))))) (= _let_37 (store (store v0 v1 v3) v2 (select v0 v2)))) (and (or (not (distinct v2 v2)) (or (=> (distinct _let_19 (ite (= v1 v2) _let_13 v2)) (ite (distinct _let_18 _let_13) (or (= _let_1 (distinct _let_31 (ite _let_1 v3 (ite (distinct v2 v2) _let_24 _let_25)))) (distinct _let_32 _let_36)) (= (= _let_12 (store _let_0 v1 (select v0 v2))) (distinct (select _let_0 v1) _let_34)))) (and (= (ite (distinct (select _let_0 v1) v3) _let_7 _let_4) _let_0) (ite (xor (and (= _let_7 (store _let_0 v1 (select v0 v2))) (= (ite (distinct (select _let_0 v1) v3) (store (store v0 v1 v3) v2 (select v0 v2)) (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) _let_0 (store (store v0 v1 v3) v2 (select v0 v2)))) (store v0 v1 v3))) (= _let_35 _let_38)) (not (distinct (store _let_4 _let_14 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)))) v0)) (= _let_21 v2))))) (or (distinct (store _let_4 _let_14 (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) _let_29 (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)))) _let_6) (= _let_34 _let_24)))) (or (and (xor (=> (or (and (not (= (ite (distinct v0 _let_0) v2 v2) _let_16)) (not _let_1)) (ite (or (ite (xor (not (distinct _let_29 _let_33)) (distinct v1 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0) (ite (= v1 v2) _let_13 v2) _let_17))) (=> (distinct _let_33 _let_27) (not (and (= (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) (ite (= (store v0 v1 v3) (store (store v0 v1 v3) v2 (select v0 v2))) (select v0 v2) (select v0 v2)) _let_24) _let_34) (= v3 (ite (distinct v2 v2) _let_24 _let_25))))) (ite (or (=> (= _let_21 _let_14) (xor (ite (= _let_35 _let_37) (= (ite (= v1 v2) (store v0 v1 v3) (store _let_0 v1 (select v0 v2))) _let_38) (distinct (ite (distinct v2 v2) _let_24 _let_25) _let_30)) (= (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) _let_13))) (=> (and (= _let_10 (store v0 v1 v3)) (distinct v1 _let_19)) (distinct _let_26 _let_26))) (and (not (distinct (ite (= v1 v2) (store v0 v1 v3) (store _let_0 v1 (select v0 v2))) (ite _let_1 _let_7 (ite (= (store (store v0 v1 v3) v2 (select v0 v2)) v0) _let_0 (ite (distinct (select _let_0 v1) v3) _let_7 _let_4))))) (distinct _let_31 _let_34)) (= (=> (distinct _let_23 (ite (distinct (select _let_0 v1) v3) (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (distinct v0 _let_0) v2 v2))) (= (store (store v0 v1 v3) v2 (select v0 v2)) v0)) (ite (or (not (distinct (ite (distinct v2 v2) _let_24 _let_25) (select v0 _let_13))) (distinct (ite _let_1 v3 (ite (distinct v2 v2) _let_24 _let_25)) _let_26)) (ite (distinct (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_15) _let_14) (ite (distinct _let_4 _let_7) (ite (= (= _let_21 _let_22) (distinct (ite (= v0 (store (store v0 v1 v3) v2 (select v0 v2))) v1 v1) (ite _let_1 v1 (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_15)))) (and (= _let_16 _let_14) (= _let_33 (select v0 v2))) (= v0 (store (store v0 v1 v3) v2 (select v0 v2)))) (distinct _let_38 _let_37)) (= (store (store v0 v1 v3) v2 (select v0 v2)) _let_0)) (= (select v0 v2) _let_25))))) (= (store v0 v1 v3) _let_37)) _let_41 _let_41)) (not (distinct _let_38 _let_0))) (not (= _let_34 v3))) (xor (and _let_39 (xor (=> (= (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_15) _let_15) (= _let_8 _let_7)) (ite (xor (xor (distinct _let_18 (ite (distinct (select _let_0 v1) v3) (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (distinct v0 _let_0) v2 v2))) (distinct _let_33 _let_34)) (xor (distinct _let_12 _let_35) (distinct _let_0 _let_35))) (distinct _let_26 _let_29) (or (distinct _let_34 v3) (=> (= _let_9 _let_4) (= _let_23 _let_16)))))) (distinct _let_18 _let_20))) (not (and (and (and (= _let_33 _let_28) (ite (or (= _let_26 _let_34) (= _let_32 _let_27)) (= _let_29 _let_32) (distinct _let_30 _let_25))) (= _let_17 _let_14)) (not (not (or (= (= (ite (distinct (select _let_0 v1) v3) (ite (distinct v2 v2) (ite (= v1 v2) _let_13 v2) _let_13) (ite (distinct v0 _let_0) v2 v2)) _let_23) (distinct _let_23 _let_14)) (distinct v1 _let_23)))))))))))))))))))))))))))))))))))))))))))))))))) ))