(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #x03e8 |_FH_0'|) (= #x0064 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| _FH_0) (= |_FH_1'| _FH_1))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (bvsge _FH_1 _FH_0)) fail))

(query fail)
