(declare-rel inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 4))
(declare-var _FH_1 (_ BitVec 4))
(declare-var _FH_2 (_ BitVec 4))
(declare-var _FH_3 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| (_ BitVec 4))
(declare-var |_FH_1'| (_ BitVec 4))
(declare-var |_FH_2'| (_ BitVec 4))
(declare-var |_FH_3'| (_ BitVec 4))

(rule (=> (and true (and (bvuge (bvadd |_FH_2'| |_FH_3'|) |_FH_1'|) (bvuge (bvadd |_FH_1'| |_FH_3'|) |_FH_2'|) (bvuge (bvadd |_FH_2'| |_FH_3'|) |_FH_0'|) (bvuge (bvadd |_FH_0'| |_FH_3'|) |_FH_2'|) (bvuge (bvadd |_FH_0'| |_FH_3'|) |_FH_1'|) (bvuge (bvadd |_FH_1'| |_FH_3'|) |_FH_0'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= _FH_2 |_FH_2'|) (distinct _FH_1 _FH_2) (= |_FH_1'| (bvadd _FH_1
       (ite (bvugt _FH_1 |_FH_0'|) #xf (ite (bvult _FH_1 |_FH_0'|) #x1 #x0)))) (= |_FH_0'| (bvadd _FH_0 (ite (bvugt _FH_0 _FH_2) #xf (ite (bvult _FH_0 _FH_2) #x1 #x0)))) (= |_FH_3'| (bvadd _FH_3 #xf)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (distinct _FH_1 _FH_2) (bvule _FH_3 #x0))) fail))

(query fail)
