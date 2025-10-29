(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))
(declare-var _FH_3 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))
(declare-var |_FH_3'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (= #x0000 |_FH_1'|) (= #x0000 |_FH_2'|) (= #x01f4 |_FH_3'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_1'| (bvadd _FH_1 #x0001)) (= |_FH_0'| #x0000) (= |_FH_3'| (bvadd _FH_3 (ite (bvuge _FH_0 #x01f4) #x0001 #xffff))) (= |_FH_2'| (bvadd _FH_2 (ite (bvult _FH_0 #x01f4) #x0001 #xffff))))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= #x08ca _FH_1) (distinct _FH_2 _FH_3))) fail))

(query fail)
