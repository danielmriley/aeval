(declare-rel inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))

(rule (=> (and true (= #x64 |_FH_2'|)) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_1'| (bvadd _FH_1 #x01)) (= #x00 _FH_1) (= |_FH_0'| (bvadd _FH_0 #x65)) (= |_FH_2'| (bvadd _FH_2 #xff)))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= #x00 _FH_1) (bvult _FH_2 #x00))) fail))

(query fail)
