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

(rule (=> (and true (and (= #x0 |_FH_0'|) (bvuge |_FH_2'| #x1) (bvugt |_FH_1'| |_FH_2'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (= _FH_2 |_FH_2'|) (= |_FH_1'| (bvadd _FH_1 #xf)) (= |_FH_0'| (bvadd _FH_0 #x1)) (bvule _FH_0 (bvadd _FH_2 #xf)))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (bvuge _FH_0 _FH_2) (bvule _FH_1 #xf))) fail))

(query fail)
