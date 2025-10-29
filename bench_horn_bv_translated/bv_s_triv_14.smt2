(declare-rel inv (Bool (_ BitVec 16)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 Bool)
(declare-var _FH_1 (_ BitVec 16))

; dstVars
(declare-var |_FH_0'| Bool)
(declare-var |_FH_1'| (_ BitVec 16))

(rule (=> (and true (= #x0000 |_FH_1'|)) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (and (= |_FH_0'| true) (= |_FH_1'| (bvadd _FH_1 (ite |_FH_0'| #x0002 #xffff))))) (inv |_FH_0'| |_FH_1'|)))

(rule (=> (and (inv _FH_0 _FH_1) (= #x3535 _FH_1)) fail))

(query fail)
