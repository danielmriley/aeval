(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #x1dba |_FH_0'|) (= #x0001 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (bvadd _FH_0 #x1dba)) (= |_FH_1'| (bvadd _FH_1 #x0001)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (distinct #x0000 _FH_1)) fail))

(query fail)
