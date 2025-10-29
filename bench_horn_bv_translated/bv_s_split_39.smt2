(declare-rel inv ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x00 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (ite (bvult (bvmul #x05 _FH_0) _FH_1) (bvadd _FH_0 #x01) (bvsdiv _FH_0 #x0a))) (= |_FH_1'| (bvadd _FH_1 (ite (bvult (bvmul #x05 _FH_0) _FH_1) #x00 #x01))))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvugt _FH_1 #x32) (bvule _FH_1 _FH_0))) fail))

(query fail)
