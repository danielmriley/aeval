(declare-rel itp ((_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))

(rule (=> (and true (= #x0 |_FH_0'|)) (itp |_FH_0'|)))

(rule (=> (and (itp _FH_0) (= (bvadd _FH_0 |_FH_0'|) #x0)) (itp |_FH_0'|)))

(rule (=> (and (itp _FH_0) (distinct _FH_0 #x0)) fail))

(query fail)
