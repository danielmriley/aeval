(declare-rel itp ((_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (bvslt #x0000 |_FH_1'|))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (= _FH_1 |_FH_1'|) (bvslt |_FH_0'| _FH_1) (= |_FH_0'| (bvadd _FH_0 #x0001)))) (itp |_FH_0'| |_FH_1'|)))

(rule (=> (and (itp _FH_0 _FH_1) (and (bvsgt _FH_1 #x2710) (bvsgt _FH_0 _FH_1))) fail))

(query fail)
