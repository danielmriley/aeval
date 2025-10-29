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

(rule (=> (and true (and (= #x0 |_FH_0'|) (bvuge |_FH_2'| #x0))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (bvadd _FH_0 (ite (= _FH_1 #x1) #x1 #x0))) (bvult _FH_0 _FH_2) (= _FH_2 |_FH_2'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (bvuge _FH_0 _FH_2) (distinct _FH_0 _FH_2))) fail))

(query fail)
