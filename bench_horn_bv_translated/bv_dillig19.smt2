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

(rule (=> (and true (and (= #x0 |_FH_0'|) (bvsge |_FH_1'| #x0) (= |_FH_1'| |_FH_2'|) (bvslt |_FH_1'| (bvadd |_FH_3'| #xf)))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3) (and (= _FH_3 |_FH_3'|) (bvsle _FH_0 (bvadd _FH_3 #xf)) (= _FH_2 |_FH_2'|) (= _FH_1 |_FH_1'|) (= |_FH_0'| (bvadd _FH_0 #x1)))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsge _FH_1 (bvadd _FH_3 #x1)) (bvsgt _FH_0 (bvadd _FH_3 #xf)))) fail))

(query fail)
