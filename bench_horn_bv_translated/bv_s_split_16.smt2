(declare-rel inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))
(declare-var _FH_2 (_ BitVec 32))
(declare-var _FH_3 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))
(declare-var |_FH_2'| (_ BitVec 32))
(declare-var |_FH_3'| (_ BitVec 32))

(rule (=> (and true (and (= #x00000000 |_FH_0'|) (= #x00000000 |_FH_1'|) (= #x00000000 |_FH_2'|) (= #x00000000 |_FH_3'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_0'| #x00000000) (= |_FH_1'| (bvadd _FH_1 #x00000001)) (= |_FH_2'| _FH_2) (= |_FH_3'| _FH_3))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= #x000f4240 _FH_1) (distinct _FH_2 _FH_3))) fail))

(query fail)
