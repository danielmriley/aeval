(declare-rel inv ((_ BitVec 32) (_ BitVec 32)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 32))
(declare-var _FH_1 (_ BitVec 32))

; dstVars
(declare-var |_FH_0'| (_ BitVec 32))
(declare-var |_FH_1'| (_ BitVec 32))

(rule (=> (and true (and (= #x00000001 |_FH_0'|) (= #xffffffff |_FH_1'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_1'| #x00000000) (= (bvadd |_FH_0'| (bvmul #x00000002 _FH_0)) #x00000000))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (bvsgt _FH_0 #x004e7be3) (distinct #x00000000 (bvadd _FH_0 _FH_1)))) fail))

(query fail)
