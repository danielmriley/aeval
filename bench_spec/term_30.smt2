(declare-rel inv (Int Int Int))
(declare-rel f (Int Int Int))

(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=> (f x y i) (inv x y i)))

(rule (=>
    (and
        (inv x y i)
        (and (> x 0) (> y 0))
        (= x1 (- x 1))
        (= y1 (- y 1))
        (= i1 (- i 1))
    )
    (inv x1 y1 i1)
  )
)

(rule (=> (and (inv x y i) (or (<= x 0) (<= y 0)) (not (= i 0))) fail))

(query fail :print-certificate true)
