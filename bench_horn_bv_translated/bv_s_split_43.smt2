(declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))

(rule (=> (and true (and (= #x00000000 |_FH_0'|) (= #x00000000 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_1'| (ite (bvuge _FH_0 #x02faf080) (bvadd _FH_1 (ite (bvuge _FH_0 #x05f5e100) #x00000000 #x00000001)) #x00000000)) (= |_FH_0'| (bvadd _FH_0 #x00000001)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvuge _FH_0 #x05f5e100) (distinct _FH_1 #x02faf080))) fail))

(query fail)
