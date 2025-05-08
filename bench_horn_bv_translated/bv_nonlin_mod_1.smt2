(declare-rel inv ((_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))

(rule (=> (and true (and (bvsgt |_FH_0'| #x0) (= |_FH_0'| |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (bvadd _FH_0 _FH_1)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) false) fail))

(query fail)
