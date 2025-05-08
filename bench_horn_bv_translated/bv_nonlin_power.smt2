(declare-rel inv ((_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))

(rule (=> (and true (and (= #x1 |_FH_1'|) (bvsgt |_FH_0'| #x0))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= _FH_0 |_FH_0'|) (= |_FH_1'| #x1))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (bvsle _FH_1 #x0)) fail))

(query fail)
