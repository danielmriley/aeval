(set-logic HORN)
(declare-rel inv ((_ BitVec 8)))
(declare-var x0 (_ BitVec 8))
(declare-var x1 (_ BitVec 8))

(declare-rel fail ())

; Init: x = 0
(rule (=> (= x0 #x00) (inv x0)))

; Trans: x' = x + 1
(rule (=> (and (inv x0) (= x1 (bvadd x0 #x01))) (inv x1)))

; Bad: x = 5
(rule (=> (and (inv x0) (= x0 #x05)) fail))

(query fail)
