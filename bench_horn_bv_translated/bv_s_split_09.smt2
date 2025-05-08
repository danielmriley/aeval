(declare-rel inv ((_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))

(rule (=> (and true (= #x0000 |_FH_0'|)) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) (= |_FH_0'| #x0000)) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) (and true (bvsgt _FH_0 #x270c))) fail))

(query fail)
