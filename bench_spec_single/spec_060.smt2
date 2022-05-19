(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (=> (< x 1000) (inv x)))

(rule (=>
    (and
        (inv x )
        (< x 1000)
        (= x1 (ite (= x 7777) x (+ x 1)))
    )
    (inv x1)
  )
)

; gh = 1000
; There should be a condition that ensures an iteration.
