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

(declare-var y1 (_ BitVec 4))
(declare-var y3 (_ BitVec 4))
(declare-var y5 (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_0'|) (= #x0 |_FH_1'|) (= #x0 |_FH_2'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (ite (and (or (bvsge y3 #x0) (bvsle y3 (bvadd y5 #x2))) (bvsle y1 y3)) (and (= |_FH_2'| y5) (= |_FH_1'| y3) (= |_FH_0'| y1)) (and (= |_FH_1'| _FH_1) (= |_FH_2'| _FH_2) (= |_FH_0'| _FH_0)))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (or (bvsgt _FH_0 _FH_1) (and (bvslt _FH_1 #x0) (bvsgt _FH_1 (bvadd _FH_2 #x2))))) fail))

(query fail)
