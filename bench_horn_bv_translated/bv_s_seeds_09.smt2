(declare-rel itp ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (and (= #x02 |_FH_0'|) (= #x01 |_FH_1'|))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (= |_FH_0'| (bvadd _FH_0 #x01)) (bvsgt _FH_0 _FH_1) (= |_FH_1'| (bvadd _FH_1 #x01)))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (bvsgt _FH_1 #x50) (bvsle _FH_0 #x51))) fail))

(query fail)
