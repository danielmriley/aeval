(declare-rel inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))
(declare-var _FH_2 (_ BitVec 32))
(declare-var _FH_3 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))
(declare-var |_FH_2'| (_ BitVec 32))
(declare-var |_FH_3'| (_ BitVec 32))

(rule (=> (and true (and (= #x00000000 |_FH_3'|) (bvsgt |_FH_0'| |_FH_1'|) (bvsgt |_FH_1'| |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_0'| (bvadd _FH_0 #x00000001)) (= |_FH_2'| (bvadd _FH_2 #x00000002)) (= |_FH_1'| (bvadd _FH_1 #x00000003)) (= |_FH_3'| _FH_3))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsgt _FH_2 (bvadd _FH_0 #x00011b53)) (bvsle _FH_3 #x00000000))) fail))

(query fail)
