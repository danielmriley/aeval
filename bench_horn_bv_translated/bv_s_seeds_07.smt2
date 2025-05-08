(declare-rel itp ((_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))

(rule (=> (and true (= #x00 |_FH_0'|)) (itp |_FH_0'|)))

(rule (=> (and (itp _FH_0) (= |_FH_0'| #x00)) (itp |_FH_0'|)))

(rule (=> (and (itp _FH_0) (bvsgt _FH_0 #x0a)) fail))

(query fail)
