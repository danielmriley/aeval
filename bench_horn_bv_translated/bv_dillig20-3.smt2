(declare-rel itp ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))
(declare-var _FH_4 (_ BitVec 4))
(declare-var _FH_5 (_ BitVec 4))
(declare-var _FH_6 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))
(declare-var |_FH_4'| (_ BitVec 4))
(declare-var |_FH_5'| (_ BitVec 4))
(declare-var |_FH_6'| (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_2'|) (= #x0 |_FH_3'|) (= (bvadd |_FH_0'| |_FH_1'|) |_FH_4'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'| |_FH_6'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6) (and (= _FH_5 |_FH_5'|) (= _FH_4 |_FH_4'|) (= _FH_6 |_FH_6'|) (bvult _FH_3 _FH_6) (= |_FH_1'| (bvadd _FH_1 (ite (= _FH_5 _FH_3) #xf #x1))) (= |_FH_3'| (bvadd _FH_3 #x1)) (= |_FH_0'| (bvadd _FH_0 (ite (= _FH_5 _FH_3) #x1 #xf))) (or (= |_FH_2'| _FH_2) (= |_FH_2'| _FH_3)))) (itp |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'| |_FH_6'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6) (and (bvugt _FH_3 #x0) (= _FH_3 _FH_6) (bvuge _FH_2 _FH_3))) fail))

(query fail)
