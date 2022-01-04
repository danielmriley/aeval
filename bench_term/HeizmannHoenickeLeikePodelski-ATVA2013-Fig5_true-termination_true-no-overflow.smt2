(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x 2))

(rule (=> 
    (and 
        (inv x y)
        (>= x 0)
        (= x1 (- x y))
        (= y1 (div (+ y 1) 2))
    )
    (inv x1 y1)
  )
)
