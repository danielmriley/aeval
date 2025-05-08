(declare-rel inv ((_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))

(rule (=> (and true (and (= #x1 |_FH_0'|) (= #x2 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvsge _FH_1 _FH_0) (= |_FH_1'| (bvadd _FH_1 #xf)) (= |_FH_0'| (bvadd _FH_0 #x2)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (distinct _FH_1 #x1) (bvslt _FH_1 _FH_0))) fail))

(query fail)
