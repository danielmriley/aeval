(declare-rel inv (Bool))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)

; dstVars
(declare-var |_FH_0'| Bool)

(rule (=> (and true (= false |_FH_0'|)) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) (= _FH_0 |_FH_0'|)) (inv |_FH_0'|)))

(rule (=> (and (inv _FH_0) _FH_0) fail))

(query fail)
