(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))
(declare-var _FH_4 (_ BitVec 4))
(declare-var _FH_5 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))
(declare-var |_FH_4'| (_ BitVec 4))
(declare-var |_FH_5'| (_ BitVec 4))

(rule (=> (and true (and (= #x1 |_FH_0'|) (= #x0 |_FH_1'|) (= #x0 |_FH_3'|) (= #x0 |_FH_4'|) (= #x0 |_FH_5'|) (= #x1 |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (and (= |_FH_4'| (bvadd _FH_4 #x1)) (= _FH_0 |_FH_0'|) (= |_FH_5'| (bvadd _FH_5 #x2)) (= |_FH_2'| (bvadd _FH_2 _FH_3)) (= _FH_1 |_FH_1'|) (= |_FH_3'| _FH_3))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (distinct _FH_3 _FH_4)) fail))

(query fail)
