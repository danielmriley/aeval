(declare-rel inv ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x32 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvslt _FH_0 #x64) (= |_FH_0'| (bvadd _FH_0 #x01)) (ite (bvsgt |_FH_0'| #x32) (= |_FH_1'| (bvadd _FH_1 #x01)) (= |_FH_1'| _FH_1)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvsgt _FH_0 #x32) (distinct _FH_1 _FH_0))) fail))

(query fail)
