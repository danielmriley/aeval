(declare-rel itp ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))
(declare-var _FH_4 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))
(declare-var |_FH_4'| (_ BitVec 4))

(rule (=> (and true (and (= #x2 |_FH_0'|) (= #x2 |_FH_1'|) (= #x2 |_FH_2'|) (= #x2 |_FH_3'|) (= #x2 |_FH_4'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (= |_FH_1'| (bvadd _FH_1 #x1)) (= |_FH_4'| (bvadd _FH_4 #x1)) (= |_FH_2'| (bvadd _FH_2 #x1)) (= |_FH_0'| (bvadd _FH_0 #x1)) (= |_FH_3'| (bvadd _FH_3 #x1)))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (or (bvsle _FH_4 #x0) (bvsle _FH_3 #x0) (bvsle _FH_1 #x0) (bvsle _FH_0 #x0) (bvsle _FH_2 #x0))) fail))

(query fail)
