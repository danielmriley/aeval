(declare-rel inv (Int))
(declare-var y Int)
(declare-var y1 Int)

(rule (inv y))

(rule (=>
    (and
        (inv y)
        (> y 0)
        (= y1 (- y 1))
    )
    (inv y1)
  )
)
