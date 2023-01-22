(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var z0 Int)
(declare-var z1 Int)
(declare-var v0 Int)
(declare-var v1 Int)
(declare-var w0 Int)
(declare-var w1 Int)

(rule (=> true (inv x0 z0 v0 w0)))

(rule (=> (and
        (inv x0 z0 v0 w0))
    (inv x1 z1 v1 w1)))

; 