(declare-rel itp ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))

(declare-var y1 (_ BitVec 4))
(declare-var y3 (_ BitVec 4))
(declare-var y5 (_ BitVec 4))
(declare-var y7 (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_0'|) (= #x0 |_FH_1'|) (= #x0 |_FH_2'|) (= #xf |_FH_3'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3) (ite (and (bvule y1 #x0) (or (bvuge y7 #x0) (bvule y7 y5)) (bvuge y1 (bvadd y7 #x1)) (= y3 y5)) (and (= |_FH_2'| y5) (= |_FH_0'| y1) (= |_FH_3'| y7) (= |_FH_1'| y3)) (and (= |_FH_2'| _FH_2) (= |_FH_0'| _FH_0) (= |_FH_1'| _FH_1) (= |_FH_3'| _FH_3)))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3) (or (and (bvult _FH_3 #x0) (bvugt _FH_3 _FH_2)) (bvult _FH_1 _FH_2) (bvugt _FH_1 _FH_2) (bvugt _FH_0 #x0) (bvult _FH_0 (bvadd _FH_3 #x1)))) fail))

(query fail)
