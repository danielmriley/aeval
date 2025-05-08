(declare-rel itp1 ((_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))

(declare-var m (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_0'|) (= #x0 |_FH_1'|))) (itp1 |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp1 _FH_0 _FH_1) (and (= |_FH_1'| (bvadd _FH_1 #x1)) (ite (= m #x1) (= |_FH_0'| (bvadd _FH_0 #x1)) (= |_FH_0'| _FH_0)))) (itp1 |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp1 _FH_0 _FH_1) (bvsgt _FH_0 _FH_1)) fail))

(query fail)
