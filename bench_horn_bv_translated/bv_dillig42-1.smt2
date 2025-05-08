(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) Bool))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 Bool)

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| Bool)

(rule (=> (and true (and (= #x1 |_FH_0'|) (= #x1 |_FH_1'|) (= |_FH_2'| #x0))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= _FH_3 |_FH_3'|) (= |_FH_2'| (bvadd _FH_0 _FH_1)) (= |_FH_1'| _FH_1) (= |_FH_0'| _FH_0))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) true) fail))

(query fail)
