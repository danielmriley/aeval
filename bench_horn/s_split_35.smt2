(declare-rel inv (Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var y0 Int)
(declare-var y1 Int)
(declare-var w0 Int)
(declare-var w1 Int)
(declare-var z0 Int)
(declare-var z1 Int)

(declare-rel fail ())

(rule (=> (and (= x0 0) (> y0 z0) (= w0 0))
    (inv x0 y0 z0 w0)))

(rule (=> (and
        (inv x0 y0 z0 w0)
        (= x1 (+ 5 x0))
        (= y1 (+ 3 y0))
        (= z1 (+ 1 z0))
        (= w1 (ite (< x0 z0) (+ w0 1) (- w0 1))))
    (inv x1 y1 z1 w1)))

(rule (=> (and (inv x0 y0 z0 w0) (> x0 y0)
    (not (<= w0 0))) fail))

(query fail)

