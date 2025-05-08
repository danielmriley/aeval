(declare-rel FUN ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))
(declare-var _FH_4 (_ BitVec 4))
(declare-var _FH_5 (_ BitVec 4))
(declare-var _FH_6 (_ BitVec 4))
(declare-var _FH_7 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))
(declare-var |_FH_4'| (_ BitVec 4))
(declare-var |_FH_5'| (_ BitVec 4))
(declare-var |_FH_6'| (_ BitVec 4))
(declare-var |_FH_7'| (_ BitVec 4))

(rule (=> (and true (and (= #x1 |_FH_3'|) (= #x1 |_FH_4'|) (= #x1 |_FH_5'|) (bvsge |_FH_2'| #x0) (bvsge |_FH_1'| #x0) (bvsge |_FH_0'| #x0))) (FUN |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'| |_FH_6'| |_FH_7'|)))

(rule (=> (and (FUN _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (and (bvsgt _FH_1 #x0) (= _FH_3 |_FH_3'|) (bvsgt _FH_2 #x0) (bvsgt _FH_0 #x0) (= _FH_4 |_FH_4'|) (= _FH_5 |_FH_5'|) (= |_FH_0'| _FH_0) (= |_FH_1'| _FH_1) (= |_FH_2'| _FH_2))) (FUN |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'| |_FH_6'| |_FH_7'|)))

(rule (=> (and (FUN _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (and (distinct _FH_0 #x0) (distinct _FH_2 #x0) (distinct _FH_1 #x0) (or (bvsle _FH_0 #x0) (bvsle _FH_2 #x0) (bvsle _FH_1 #x0)))) fail))

(query fail)
