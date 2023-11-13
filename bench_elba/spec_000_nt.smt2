(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var N Int)

(rule (inv x N))

(rule (=>
    (and
        (inv x N)
        (not (= x N))
        (= x1 (- x 1))
    )
    (inv x1 N)
  )
)
