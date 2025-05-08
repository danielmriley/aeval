(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
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

(rule (=> (and true (and (bvsge (bvadd |_FH_2'| |_FH_3'|) |_FH_1'|) (bvsge (bvadd |_FH_1'| |_FH_3'|) |_FH_2'|) (bvsge (bvadd |_FH_2'| |_FH_3'|) |_FH_0'|) (bvsge (bvadd |_FH_0'| |_FH_3'|) |_FH_2'|) (bvsge (bvadd |_FH_0'| |_FH_3'|) |_FH_1'|) (bvsge (bvadd |_FH_1'| |_FH_3'|) |_FH_0'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= _FH_2 |_FH_2'|) (distinct _FH_1 _FH_2) (= |_FH_1'| _FH_1) (= |_FH_0'| _FH_0) (= |_FH_3'| (bvadd _FH_3 #xf)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (distinct _FH_1 _FH_2) (bvsle _FH_3 #x0))) fail))

(query fail)
