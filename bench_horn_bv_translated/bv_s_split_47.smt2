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

(rule (=> (and true (and (= #x0000 |_FH_0'|) (= #x0000 |_FH_2'|) (bvuge |_FH_1'| #x0000))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (bvadd _FH_0 #x0001)) (= |_FH_2'| (let ((a!1 (ite (bvult _FH_0 (bvadd (bvmul #x0309 _FH_1) #x0f2d)) #x0001 #x0000)))
  (bvadd _FH_2 (ite (bvuge _FH_0 (bvmul #x0309 _FH_1)) a!1 #x0000)))))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvuge _FH_0 (bvadd (bvmul #x0309 _FH_1) #x1e5a)) (distinct _FH_2 #x0f2d))) fail))

(query fail)
