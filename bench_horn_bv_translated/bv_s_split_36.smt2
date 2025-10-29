(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #xd8f0 |_FH_0'|) (= #x0000 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_1'| (ite (bvuge _FH_1 _FH_0) (bvneg _FH_0) (bvadd _FH_1 #x0002))) (= |_FH_0'| (bvadd _FH_0 (ite (bvuge _FH_1 _FH_0) #x0001 #x0000))))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvuge _FH_0 #x0000) (bvult _FH_0 (bvadd _FH_1 #xffff)))) fail))

(query fail)
