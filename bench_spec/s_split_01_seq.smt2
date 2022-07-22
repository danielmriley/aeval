(declare-rel inv (Int Int ))
(declare-rel inv2 (Int Int ))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)

(rule (=> (and (= x0 0) (= y0 5000))
    (inv x0 y0)))

(rule (=> (and
        (inv x0 y0)
        (< x0 5000)
        (= x1 (+ x0 1))
        (= y1 y0))
    (inv x1 y1)))

(rule (=> (inv x0 y0) (inv2 x0 y0)))

(rule (=> (and
        (inv2 x0 y0)
        (< x0 10000)
        (= x1 (+ x0 1))
        (= y1 (+ y0 1)))
    (inv2 x1 y1)))
