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

(rule (=> (and true (= #x00000000 |_FH_0'|)) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_0'| (bvadd _FH_0 #x00000001)) (= |_FH_1'| (ite (bvuge _FH_0 #x000bae70) (bvadd _FH_1 (ite (bvuge _FH_0 #x000d3510) #x00000000 #x00000001)) #x00000000)) (= |_FH_2'| (ite (bvuge _FH_0 #x000a1eda) (bvadd _FH_2 (ite (bvuge _FH_0 #x000ba57a) #x00000000 #x00000001)) #x00000000)))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvuge _FH_0 #x000ebbb0) (distinct _FH_1 _FH_2))) fail))

(query fail)
