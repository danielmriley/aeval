(declare-rel inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))
(declare-var _FH_2 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))
(declare-var |_FH_2'| (_ BitVec 32))

(rule (=> (and true (and (= #x00000000 |_FH_0'|) (= #x00000000 |_FH_1'|) (= #x00000000 |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_1'| (bvadd _FH_0 _FH_1)) (= |_FH_0'| (bvadd _FH_0 #x00000001)) (= |_FH_2'| _FH_2))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvsge _FH_0 #x0034adcd) (bvsle _FH_2 #x00000000))) fail))

(query fail)
