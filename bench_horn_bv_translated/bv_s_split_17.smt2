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

(rule (=> (and true (and (= #x0000 |_FH_2'|) (= #x0000 |_FH_3'|) (bvugt |_FH_0'| |_FH_1'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_1'| (bvadd _FH_1 #x0002)) (= |_FH_0'| (bvadd _FH_0 #x0001)) (= |_FH_2'| (bvadd _FH_2 (ite (bvult _FH_0 _FH_1) #x0001 #x0000))) (= |_FH_3'| (bvadd _FH_3 (ite (bvult _FH_0 _FH_1) #x0000 #x0001))))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvugt _FH_2 #x03e8) (bvule _FH_3 #x0000))) fail))

(query fail)
