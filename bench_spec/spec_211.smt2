(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(rule (=> (= (mod x 5) 0) (inv x)))

(rule (=>
    (and
        (inv x)
        (>= x 0)
        (= x1 (- x 5))
    )
    (inv x1)
  )
)
