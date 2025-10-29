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

(rule (=> (and true (and (= #x0fa0 |_FH_0'|) (= #x07d0 |_FH_1'|) (= #x0000 |_FH_2'|) (= #x0000 |_FH_3'|) (bvugt |_FH_4'| #x0000) (bvult |_FH_4'| #x000a))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (= _FH_4 |_FH_4'|) (= _FH_1 |_FH_1'|) (bvult _FH_3 _FH_4) (= |_FH_3'| (bvadd _FH_3 #x0001)) (= _FH_0 |_FH_0'|) (= |_FH_2'| (bvadd _FH_2 (ite (= (ite true #x0000 #x0001) #x0000) _FH_0 _FH_1))))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (bvuge _FH_3 _FH_4) (bvule _FH_2 _FH_4))) fail))

(query fail)
