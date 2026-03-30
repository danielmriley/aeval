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

(rule (=> (and true (and (= #x0001 |_FH_0'|) (= #x0001 |_FH_1'|) (= #x0001 |_FH_2'|))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (= |_FH_1'| (bvmul #x0002 _FH_0)) (= |_FH_2'| (bvmul #x0003 _FH_0)) (= |_FH_0'| (bvadd _FH_0 #x0001)))) (itp |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (itp _FH_0 _FH_1 _FH_2) (and (bvuge _FH_2 (bvadd _FH_1 #x01f4)) (bvuge _FH_0 #x03e8))) fail))

(query fail)
