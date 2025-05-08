(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))
(declare-var _FH_3 (_ BitVec 16))
(declare-var _FH_4 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))
(declare-var |_FH_3'| (_ BitVec 16))
(declare-var |_FH_4'| (_ BitVec 16))

(declare-var w0 (_ BitVec 16))

(rule (=> (and true (and (= #x0fa0 |_FH_0'|) (= #x07d0 |_FH_1'|) (= #x0000 |_FH_2'|) (= #x0000 |_FH_3'|) (bvsgt |_FH_4'| #x0000) (bvslt |_FH_4'| #x000a))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (= _FH_4 |_FH_4'|) (= _FH_1 |_FH_1'|) (bvslt _FH_3 _FH_4) (= |_FH_3'| (bvadd _FH_3 #x0001)) (= _FH_0 |_FH_0'|) (= |_FH_2'| _FH_2))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (bvsge _FH_3 _FH_4) (bvsle _FH_2 _FH_4))) fail))

(query fail)
