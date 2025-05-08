(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (= |_FH_0'| (bvadd |_FH_1'| #xfa38))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvsgt |_FH_1'| |_FH_0'|) (bvslt _FH_1 _FH_0))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvsge _FH_0 #x0000) (bvsle _FH_1 #x0000))) fail))

(query fail)
