(declare-rel itp ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))

(rule (=> (and true (and (= #x0000 |_FH_0'|) (bvsgt |_FH_2'| #x0000) (bvslt |_FH_2'| #x0005) (= |_FH_1'| (bvmul #x0003 |_FH_2'|)))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (bvslt _FH_0 #x00c8) (= |_FH_1'| (bvadd _FH_1 #x0001)) (= _FH_2 |_FH_2'|) (= |_FH_0'| (bvadd _FH_0 #x0001)))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (or (bvslt _FH_1 #x0003) (bvsgt _FH_1 #x00d4))) fail))

(query fail)
