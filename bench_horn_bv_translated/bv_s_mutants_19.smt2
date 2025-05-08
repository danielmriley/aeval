(declare-rel inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel fail ())

; srcVars
(declare-var _FH_0 (_ BitVec 8))
(declare-var _FH_1 (_ BitVec 8))
(declare-var _FH_2 (_ BitVec 8))
(declare-var _FH_3 (_ BitVec 8))
(declare-var _FH_4 (_ BitVec 8))

; dstVars
(declare-var |_FH_0'| (_ BitVec 8))
(declare-var |_FH_1'| (_ BitVec 8))
(declare-var |_FH_2'| (_ BitVec 8))
(declare-var |_FH_3'| (_ BitVec 8))
(declare-var |_FH_4'| (_ BitVec 8))

(rule (=> (and true (and (= #x64 |_FH_0'|) (= #x00 |_FH_1'|) (= #x00 |_FH_3'|) (= #x00 |_FH_2'|) (or (= |_FH_4'| #x00) (= |_FH_4'| #x01)))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (= |_FH_3'| (bvadd _FH_3 #x01)) (= |_FH_2'| _FH_2) (= |_FH_4'| #x00) (= |_FH_1'| _FH_1) (bvslt _FH_3 (bvmul #x02 _FH_0)) (= _FH_0 |_FH_0'|))) (inv |_FH_0'| |_FH_1'| |_FH_2'| |_FH_3'| |_FH_4'|)))

(rule (=> (and (inv _FH_0 _FH_1 _FH_2 _FH_3 _FH_4) (and (bvsge _FH_3 (bvmul #x02 _FH_0)) false)) fail))

(query fail)
