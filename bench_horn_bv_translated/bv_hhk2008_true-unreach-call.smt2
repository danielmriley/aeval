(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))
(declare-var _FH_3 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))
(declare-var |_FH_3'| (_ BitVec 16))

(rule (=> (and true (and (= |_FH_0'| |_FH_2'|) (bvsle |_FH_0'| #x2710) (= |_FH_1'| |_FH_3'|) (bvsle #x0000 |_FH_1'|) (bvsle |_FH_1'| #x2710))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsgt _FH_3 #x0000) (= |_FH_2'| (bvadd _FH_2 #x0001)) (= _FH_1 |_FH_1'|) (= _FH_0 |_FH_0'|) (= |_FH_3'| (bvadd _FH_3 #xffff)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (bvsle _FH_3 #x0000) (distinct _FH_2 (bvadd _FH_0 _FH_1)))) fail))

(query fail)
