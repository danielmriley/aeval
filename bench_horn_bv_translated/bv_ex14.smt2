(declare-rel itp ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))

(rule (=> (and true (= #x1 |_FH_0'|)) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (= _FH_2 |_FH_2'|) (bvsle _FH_0 _FH_2) (= (bvadd _FH_0 |_FH_1'|) _FH_2) (= |_FH_0'| (bvadd _FH_0 #x1)))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (bvsle _FH_0 _FH_2) (or (bvslt _FH_2 _FH_0) (bvsge #x0 _FH_0)))) fail))

(query fail)
