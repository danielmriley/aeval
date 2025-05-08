(declare-rel inv ((_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))

(rule (=> (and true (= #x0 |_FH_0'|)) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) (= |_FH_0'| (bvadd _FH_0 #x2))) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) false) fail))

(query fail)
