(declare-rel inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))
(declare-var _FH_3 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))
(declare-var |_FH_3'| (_ BitVec 8))

(rule (=> (and true (and (= #x64 |_FH_1'|) (= #x01 |_FH_2'|) (bvsgt |_FH_0'| #x00) (bvsge |_FH_3'| |_FH_0'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsgt _FH_0 #x00) (= |_FH_3'| (bvadd _FH_3 #xff)) (= (bvadd |_FH_0'| _FH_1) _FH_0) (= (bvadd _FH_2 |_FH_2'|) #x00) (= (bvadd |_FH_1'| _FH_2) _FH_1))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsgt _FH_0 #x00) (bvslt _FH_3 #x00))) fail))

(query fail)
