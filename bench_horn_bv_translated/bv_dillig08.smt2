(declare-rel inv ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x00 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (or (and (= |_FH_0'| (bvadd _FH_0 #x01)) (= |_FH_1'| (bvadd _FH_1 #x64))) (and (= |_FH_0'| _FH_0) (= |_FH_1'| _FH_1)) (and (= (bvsub |_FH_0'| _FH_0) #x00) (= (bvsub |_FH_1'| _FH_1) #x00)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvuge _FH_0 #x04) (bvule _FH_1 #x02))) fail))

(query fail)
