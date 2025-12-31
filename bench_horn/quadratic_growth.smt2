(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var xp Int)
(declare-var yp Int)

(declare-rel fail ())

; Init: x=0, y=0 => inv(x, y)
(rule (=> (and (= x 0) (= y 0)) (inv x y)))

; Trans: inv(x, y) /\ xp = x + 1 /\ yp = y + x => inv(xp, yp)
(rule (=> (and (inv x y) (= xp (+ x 1)) (= yp (+ y x))) (inv xp yp)))

; Property: inv(x, y) /\ not (2y = x(x-1)) => fail
; 2y = x*x - x
(rule (=> (and (inv x y) (not (= (* 2 y) (- (* x x) x)))) fail))

(query fail :print-certificate true)
