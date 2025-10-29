(declare-rel itp ((_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))

(rule (=> (and true (= #x00 |_FH_0'|)) (itp |_FH_0'|)))

(rule (=> (and (itp _FH_0) (= |_FH_0'| (ite (= _FH_0 #x0a) #x00 (bvadd _FH_0 #x01)))) (itp |_FH_0'|)))

(rule (=> (and (itp _FH_0) (bvugt _FH_0 #x0a)) fail))

(query fail)
