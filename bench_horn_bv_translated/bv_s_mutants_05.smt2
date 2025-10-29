(declare-rel itp ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (bvugt |_FH_1'| #x0000))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (= |_FH_1'| (bvadd _FH_1 #x0002)) (= |_FH_0'| (bvadd _FH_0 #x0001)))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (bvule _FH_1 #x07d0) (bvugt _FH_0 #x03e8))) fail))

(query fail)
