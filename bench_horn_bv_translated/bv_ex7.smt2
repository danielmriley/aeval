(declare-rel itp ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_2'|) (= |_FH_0'| |_FH_3'|) (bvsge |_FH_1'| #x0) (bvslt |_FH_1'| |_FH_0'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3) (and (= _FH_1 |_FH_1'|) (bvslt _FH_2 _FH_1) (= |_FH_2'| (bvadd _FH_2 #x1)) (= _FH_3 |_FH_3'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3) (and (bvslt _FH_2 _FH_1) (or (bvslt _FH_2 #x0) (bvsge _FH_2 _FH_3)))) fail))

(query fail)
