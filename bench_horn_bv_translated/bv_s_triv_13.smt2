(declare-rel inv (Bool (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| (_ BitVec 4))

(rule (=> (and true (and |_FH_0'| (= #x0 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (= |_FH_1'| (bvadd _FH_1 #x1))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (bvult _FH_1 #x0)) fail))

(query fail)
