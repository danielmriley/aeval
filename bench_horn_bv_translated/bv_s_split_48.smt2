(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (= #x0000 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (bvadd _FH_0 #x0001)) (= |_FH_1'| (bvadd _FH_1
       (ite (bvult _FH_0 #x1388)
            (ite (bvuge _FH_0 #x0fa0) #x0004 #x0001)
            (ite (bvuge _FH_0 #x1770) #xffff #xfffc)))))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= #x2710 _FH_0) (distinct _FH_1 #x0000))) fail))

(query fail)
