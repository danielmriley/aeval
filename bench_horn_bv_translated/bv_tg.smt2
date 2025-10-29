(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))

(declare-var x1 (_ BitVec 4))
(declare-var y1 (_ BitVec 4))
(declare-var z1 (_ BitVec 4))

(rule (=> (and true (= #x0 |_FH_0'|)) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (ite (bvuge _FH_0 #x5) (and (= y1 (bvadd _FH_1 #x1)) (= x1 _FH_0) (= z1 _FH_2)) (and (= z1 _FH_2) (= y1 _FH_1) (= x1 (bvadd _FH_0 #x1)))) (ite (bvule y1 #x5) (and (= |_FH_2'| (bvadd z1 #x1)) (= |_FH_1'| y1) (= |_FH_0'| x1)) (ite (bvugt x1 y1) (and (= |_FH_0'| x1) (= |_FH_2'| z1) (= |_FH_1'| (bvadd y1 #x1))) (and (= |_FH_1'| y1) (= |_FH_2'| z1) (= |_FH_0'| #x0)))))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvugt y1 #x5) (= x1 _FH_0) (= z1 _FH_2) (= y1 (bvadd _FH_1 #x1)) (bvugt x1 y1))) fail))

(query fail)
