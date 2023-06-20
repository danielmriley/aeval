; Three loops, but only two will execute on any given execution.
; BOUND: gh = x + y

(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-rel inv3 (Int Int))
(declare-rel inv4 (Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var x2 Int)
(declare-var y2 Int)

(declare-rel fail ())

(rule (=> true (inv1 x1 y1)))

(rule (=>
    (and
      (inv1 x1 y1)
      (> x1 0)
      (> y1 0)
      (= x2 (- x1 1))
      (= y2 (- y1 1))
    )
    (inv1 x2 y2)
  )
)

(rule (=> (inv1 x1 y1) (inv2 x1 y1)))

(rule (=>
    (and
      (inv2 x1 y1)
      (> y1 0)
      (= y2 (- y1 1))
    )
    (inv2 x2 y2)
  )
)

(rule (=> (inv2 x1 y1) (inv3 x1 y1)))

(rule (=>
    (and
      (inv3 x1 y1)
      (> x1 0)
      (= x2 (- x1 1))
    )
    (inv3 x2 y2)
  )
)
