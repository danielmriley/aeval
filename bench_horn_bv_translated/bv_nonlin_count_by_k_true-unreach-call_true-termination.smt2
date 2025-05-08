(declare-rel itp ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (bvsle #x00 |_FH_1'|) (bvsle |_FH_1'| #x0a) (bvsge |_FH_2'| #x00))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (bvadd _FH_0 _FH_1)) (bvslt _FH_0 #x01) (= _FH_2 |_FH_2'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (bvsge _FH_0 #x01) (distinct _FH_0 #x01))) fail))

(query fail)
