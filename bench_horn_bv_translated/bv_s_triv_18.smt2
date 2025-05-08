(declare-rel inv (Bool (_ BitVec 64)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 (_ BitVec 64))

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| (_ BitVec 64))

(rule (=> (and true (and (= false |_FH_0'|) (= #x00000000000d3577 |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and |_FH_0'| (= |_FH_1'| (bvadd (bvmul #x000000000003cbc4 _FH_1) #x000000004ef0379e)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and _FH_0 (bvslt _FH_1 #x0000003272d783ba))) fail))

(query fail)
