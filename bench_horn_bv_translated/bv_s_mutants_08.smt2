(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #xff9c |_FH_0'|) (= #xff38 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_1'| (bvadd |_FH_0'| #x0002)) (= |_FH_0'| (bvadd _FH_0 #x0001)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvsle _FH_1 #x0000) (bvsgt _FH_0 #x0000))) fail))

(query fail)
