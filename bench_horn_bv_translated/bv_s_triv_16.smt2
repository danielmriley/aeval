(declare-rel inv (Bool Bool Bool Bool (_ BitVec 4)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 Bool)
(declare-var _FH_2 Bool)
(declare-var _FH_3 Bool)
(declare-var _FH_4 (_ BitVec 4))

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| Bool)
(declare-var |_FH_2'| Bool)
(declare-var |_FH_3'| Bool)
(declare-var |_FH_4'| (_ BitVec 4))

(rule (=> (and true (= #x0 |_FH_4'|)) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (= |_FH_4'| (bvadd _FH_4 #x1)) (or |_FH_0'| (not true)) (or |_FH_1'| (not false)) (or |_FH_2'| (not false)) (or |_FH_3'| (not false)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (not _FH_0) (not _FH_3) (not _FH_1) (bvugt _FH_4 #x0) (not _FH_2))) fail))

(query fail)
