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

(rule (=> (and true (and (= #x1 |_FH_2'|) (bvult |_FH_1'| #x0) (bvugt |_FH_0'| #x0))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_2'| (ite (bvuge _FH_1 #x0) (bvmul #x2 _FH_2) _FH_2)) (= |_FH_1'| (bvadd _FH_1 #x2)) (= |_FH_0'| (bvadd _FH_0 #x1)))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvule _FH_2 #x1) (bvuge _FH_1 _FH_0))) fail))

(query fail)
