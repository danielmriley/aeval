(declare-rel inv ((_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))

(rule (=> (and true (= #x0000 |_FH_0'|)) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) (= |_FH_0'| (bvadd _FH_0 #x5bac))) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) false) fail))

(query fail)
