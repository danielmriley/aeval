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

(rule (=> (and true (and (= #x0001 |_FH_0'|) (= #x0001 |_FH_1'|) (= #x03e8 |_FH_3'|) (bvsle #x0000 |_FH_2'|) (bvsle |_FH_2'| #x0001) (bvslt #x03e8 |_FH_4'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (bvslt _FH_0 _FH_4) (= _FH_4 |_FH_4'|) (= |_FH_2'| (bvadd _FH_2 #xffff)) (= |_FH_0'| (bvadd _FH_0 #x0001)) (= _FH_3 |_FH_3'|) (= |_FH_1'| (bvadd _FH_1 _FH_2)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (bvslt _FH_0 _FH_4) (or (bvsgt (bvadd _FH_0 _FH_2) #x0002) (bvslt _FH_0 #x0001) (bvsgt #x0001 (bvadd _FH_0 _FH_2))))) fail))

(query fail)
