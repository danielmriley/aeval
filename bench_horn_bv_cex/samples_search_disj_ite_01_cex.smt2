(declare-rel itp ((_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x64 |_FH_1'|))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (= |_FH_1'| (bvadd (ite (bvugt |_FH_0'| #x00) #x01 #x00)
       (ite (bvugt _FH_1 #x0a) #xff _FH_1))) (= |_FH_0'| (bvadd _FH_0 #x01)))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (bvugt _FH_0 #x0a) (distinct _FH_1 _FH_0))) fail))

(query fail)
