(declare-rel inv (Bool Bool))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 Bool)

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| Bool)

(rule (=> (and true (= |_FH_1'| (not |_FH_0'|))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| (not _FH_1)) (= |_FH_1'| (not _FH_0)))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and _FH_0 _FH_1)) fail))

(query fail)
