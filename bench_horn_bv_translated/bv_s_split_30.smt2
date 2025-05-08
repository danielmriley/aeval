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

(rule (=> (and true (and (= #x00000034 |_FH_0'|) (= #x00000061 |_FH_1'|) (= #x00000000 |_FH_3'|) (= #xffffffb4 |_FH_2'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= (bvadd |_FH_1'| (bvmul #x00000002 _FH_1)) #x00000036) (= (bvadd |_FH_0'| (bvmul #x00000007 _FH_0)) #x0000000d) (= (bvadd |_FH_2'| (bvmul #x00000005 _FH_0)) (bvadd (bvmul #x00000003 _FH_1) (bvmul #x00000004 _FH_2))) (= |_FH_3'| _FH_3))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsge _FH_1 #x00013c12) (bvsle _FH_3 #x00000000))) fail))

(query fail)
