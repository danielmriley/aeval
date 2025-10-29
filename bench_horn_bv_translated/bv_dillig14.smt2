(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_0'|) (= #x1 |_FH_1'|) (bvugt |_FH_2'| #x0))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= _FH_2 |_FH_2'|) (bvule _FH_1 _FH_2) (or (= |_FH_0'| (bvadd _FH_0 #xf)) (= |_FH_0'| (bvadd _FH_0 #x1))) (= |_FH_1'| (bvadd _FH_1 #x1)))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (or (bvult (bvadd _FH_0 _FH_2) #x0) (bvugt _FH_0 _FH_2)) (bvugt _FH_1 _FH_2))) fail))

(query fail)
