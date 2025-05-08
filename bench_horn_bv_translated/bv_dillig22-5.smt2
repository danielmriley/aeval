(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
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

(rule (=> (and true (and (= #x0 |_FH_0'|) (= #x0 |_FH_1'|) (= #x0 |_FH_2'|) (bvsge |_FH_3'| #x0))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_2'| (bvadd |_FH_0'| |_FH_1'|)) (= _FH_3 |_FH_3'|) (= |_FH_0'| _FH_0) (bvslt _FH_1 _FH_3) (= |_FH_1'| (bvadd _FH_1 #x1)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsge _FH_1 _FH_3) (distinct _FH_3 _FH_0))) fail))

(query fail)
