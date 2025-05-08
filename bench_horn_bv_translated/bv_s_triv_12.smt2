(declare-rel inv (Bool Bool Bool Bool))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 Bool)
(declare-var _FH_2 Bool)
(declare-var _FH_3 Bool)

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| Bool)
(declare-var |_FH_2'| Bool)
(declare-var |_FH_3'| Bool)

(rule (=> (and true (and (= |_FH_0'| (not |_FH_1'|)) (= |_FH_2'| (not |_FH_3'|)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= |_FH_3'| (not _FH_3)) (= |_FH_1'| (not _FH_1)) (= |_FH_0'| (not _FH_0)) (= |_FH_2'| (not _FH_2)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3) (and (= _FH_1 _FH_2) (distinct _FH_0 _FH_3))) fail))

(query fail)
