(declare-rel inv (Bool Bool Bool Bool (_ BitVec 4) (_ BitVec 4) (_ BitVec 4) (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 Bool)
(declare-var _FH_2 Bool)
(declare-var _FH_3 Bool)
(declare-var _FH_4 (_ BitVec 4))
(declare-var _FH_5 (_ BitVec 4))
(declare-var _FH_6 (_ BitVec 4))
(declare-var _FH_7 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| Bool)
(declare-var |_FH_2'| Bool)
(declare-var |_FH_3'| Bool)
(declare-var |_FH_4'| (_ BitVec 4))
(declare-var |_FH_5'| (_ BitVec 4))
(declare-var |_FH_6'| (_ BitVec 4))
(declare-var |_FH_7'| (_ BitVec 4))

(rule (=> (and true (and (= #x0 |_FH_4'|) (= #x0 |_FH_5'|) (= #x0 |_FH_6'|) (= #x0 |_FH_7'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'| |_FH_6'| |_FH_7'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (or (and |_FH_0'| (= |_FH_5'| _FH_5) (= |_FH_4'| (bvadd _FH_4 #x1)) (= |_FH_6'| _FH_6) (= |_FH_7'| _FH_7)) (and |_FH_1'| (= |_FH_5'| (bvadd _FH_5 #x1)) (= |_FH_4'| _FH_4) (= |_FH_6'| _FH_6) (= |_FH_7'| _FH_7)) (and |_FH_2'| (= |_FH_5'| _FH_5) (= |_FH_4'| _FH_4) (= |_FH_6'| (bvadd _FH_6 #x1)) (= |_FH_7'| _FH_7)) (and |_FH_3'| (= |_FH_5'| _FH_5) (= |_FH_4'| _FH_4) (= |_FH_6'| _FH_6) (= |_FH_7'| (bvadd _FH_7 #x1))))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'| |_FH_5'| |_FH_6'| |_FH_7'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4 _FH_5 _FH_6 _FH_7) (and (not _FH_0) (not _FH_1) (bvsgt (bvadd _FH_4 _FH_5) #x0) (not _FH_3) (not _FH_2))) fail))

(query fail)
