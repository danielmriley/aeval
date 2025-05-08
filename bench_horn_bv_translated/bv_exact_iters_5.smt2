(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (= #x03e8 |_FH_1'|) (= #x0000 |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= |_FH_2'| (bvadd _FH_2 #x0002)) (= |_FH_0'| (bvadd _FH_0 #x0001)) (= |_FH_1'| (bvadd _FH_1 #xfffd)))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (distinct _FH_1 #x0190) (= (bvadd _FH_0 _FH_2) #x0258))) fail))

(query fail)
