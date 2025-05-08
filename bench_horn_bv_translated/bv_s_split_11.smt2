(declare-rel inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))
(declare-var _FH_2 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))
(declare-var |_FH_2'| (_ BitVec 32))

(rule (=> (and true (and (or (= |_FH_2'| #x00000000) (= |_FH_2'| #x00000001)) (bvslt |_FH_0'| #x00000000) (bvsgt |_FH_1'| |_FH_0'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_0'| (bvadd _FH_0 #x00000001)) (= _FH_2 |_FH_2'|) (= |_FH_1'| _FH_1))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvsgt _FH_0 #x0000d694) (bvsle _FH_1 #x0000d694))) fail))

(query fail)
