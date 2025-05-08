(declare-rel inv ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x0a |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (bvadd _FH_0 #x02)) (= |_FH_1'| (bvadd _FH_1 #xff)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= #x04 _FH_0) (distinct _FH_1 #x08))) fail))

(query fail)
