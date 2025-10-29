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

(rule (=> (and true (and (= #x0000 |_FH_0'|) (= #x00c8 |_FH_1'|) (= #x0190 |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_0'| (bvadd _FH_0 #x0001)) (= |_FH_1'| (bvadd _FH_1 (ite (bvult _FH_0 #x00c8) #x0001 #x0000))) (= |_FH_2'| (bvadd _FH_2 (ite (bvult _FH_0 #x00c8) #x0000 #x0002))))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvuge _FH_1 #x0190) (distinct _FH_2 (bvmul #x0002 _FH_0)))) fail))

(query fail)
