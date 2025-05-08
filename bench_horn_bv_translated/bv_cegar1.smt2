(declare-rel inv ((_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))

(rule (=> (and true (and (bvsge |_FH_0'| #x0) (bvsle |_FH_0'| #x2) (bvsge |_FH_1'| #x0) (bvsle |_FH_1'| #x2))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (bvadd _FH_0 #x2)) (= |_FH_1'| (bvadd _FH_1 #x2)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= #x4 _FH_0) (= #x0 _FH_1))) fail))

(query fail)
