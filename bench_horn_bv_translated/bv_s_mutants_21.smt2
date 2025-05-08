(declare-rel itp ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))

(declare-var x9 (_ BitVec 8))

(rule (=> (and true (and (bvsgt x9 #x00) (bvslt x9 #x0a) (= #x00 |_FH_0'|) (= #x00 |_FH_1'|) (= (bvmul #x0a x9) |_FH_2'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (= |_FH_2'| (bvadd |_FH_0'| |_FH_1'|)) (or (and (= |_FH_1'| (bvadd _FH_1 #x01)) (= |_FH_0'| (bvadd _FH_0 #xff))) (and (= |_FH_1'| (bvadd _FH_1 #xff)) (= |_FH_0'| (bvadd _FH_0 #x01)))))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (= #x4e _FH_2)) fail))

(query fail)
