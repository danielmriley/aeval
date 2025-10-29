(declare-rel inv ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (= #xce |_FH_0'|)) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_1'| (bvadd _FH_1 #x01)) (bvult _FH_0 #x00) (= |_FH_0'| (bvadd _FH_0 _FH_1)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvuge _FH_0 #x00) (bvule _FH_1 #x00))) fail))

(query fail)
