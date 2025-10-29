(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (= #x1f40 |_FH_1'|) (= #x0000 |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_1'| (bvadd _FH_1 (ite (bvuge _FH_0 #x1f40) #x0001 #xffff))) (= |_FH_0'| (bvadd _FH_0 #x0001)) (= |_FH_2'| (bvadd _FH_2 (ite (bvult _FH_0 #x1f40) #x0001 #xffff))))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= #x3e80 _FH_0) (or (bvult _FH_1 #x1f40) (bvugt _FH_1 #x1f40) (bvult _FH_2 #x0000) (bvugt _FH_2 #x0000)))) fail))

(query fail)
