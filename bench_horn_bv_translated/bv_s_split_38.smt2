(declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))

(rule (=> (and true (and (= #x0000c350 |_FH_0'|) (= #x00000000 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (bvadd _FH_0 (ite (bvuge _FH_1 _FH_0) #x00000005 #x00000000))) (= |_FH_1'| (bvadd _FH_1 (ite (bvuge _FH_1 _FH_0) #x00000000 #x00000001))))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvugt _FH_1 #x0000c350) (bvugt _FH_0 (bvadd _FH_1 #x00000005)))) fail))

(query fail)
