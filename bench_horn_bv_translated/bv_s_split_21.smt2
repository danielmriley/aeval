(declare-rel inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))
(declare-var _FH_3 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))
(declare-var |_FH_3'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x01 |_FH_1'|) (= #x00 |_FH_2'|) (= #x01 |_FH_3'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_0'| (bvadd _FH_0 #x01)) (= (bvadd _FH_3 |_FH_3'|) #x01) (= |_FH_1'| (bvadd _FH_1 #x02)) (= |_FH_2'| (ite (= #x00 _FH_3) (bvadd _FH_2 #x01) #x00)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= #x0a _FH_0) (distinct _FH_2 #x0a))) fail))

(query fail)
