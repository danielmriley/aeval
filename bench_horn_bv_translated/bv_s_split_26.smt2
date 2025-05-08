(declare-rel inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))

(rule (=> (and true (and (= #x00 |_FH_0'|) (= #x00 |_FH_2'|) (bvsge |_FH_1'| #x19))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (= _FH_1 |_FH_1'|) (= |_FH_0'| (bvadd _FH_0 #x01)) (= |_FH_2'| _FH_2))) (inv |_FH_0'| |_FH_1'| |_FH_2'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2) (and (bvsle _FH_2 #x00) (bvsgt _FH_0 (bvmul #x32 _FH_1)))) fail))

(query fail)
