(declare-rel inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 16))
(declare-var _FH_1 (_ BitVec 16))
(declare-var _FH_2 (_ BitVec 16))
(declare-var _FH_3 (_ BitVec 16))
(declare-var _FH_4 (_ BitVec 16))
(declare-var _FH_5 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| (_ BitVec 16))
(declare-var |_FH_1'| (_ BitVec 16))
(declare-var |_FH_2'| (_ BitVec 16))
(declare-var |_FH_3'| (_ BitVec 16))
(declare-var |_FH_4'| (_ BitVec 16))
(declare-var |_FH_5'| (_ BitVec 16))

(rule (=> (and true (and (= #x0001 |_FH_0'|) (= #x0001 |_FH_1'|) (= #x0001 |_FH_2'|) (= #x0001 |_FH_3'|) (= #x0001 |_FH_4'|) (= #x0001 |_FH_5'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (and (= |_FH_0'| |_FH_1'|) (= |_FH_0'| |_FH_2'|) (= |_FH_0'| |_FH_3'|) (= |_FH_0'| |_FH_4'|) (= |_FH_0'| |_FH_5'|) (= |_FH_0'| (bvadd _FH_0 _FH_1)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5) (bvuge _FH_0 #x2710)) fail))

(query fail)
