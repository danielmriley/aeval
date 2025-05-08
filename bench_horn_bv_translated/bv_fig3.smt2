(declare-rel FUN ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
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

(rule (=> (and true (and (= |_FH_2'| #x0) (= |_FH_1'| |_FH_0'|))) (FUN |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (FUN _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_2'| #x0) (= |_FH_1'| |_FH_0'|) (= |_FH_0'| _FH_1) (distinct _FH_0 |_FH_0'|))) (FUN |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (FUN _FH_0 _FH_1 _FH_2 _FH_3) (and (distinct _FH_2 #x1) (= _FH_0 _FH_1))) fail))

(query fail)
