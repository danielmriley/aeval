(declare-rel inv (Int Int))
(declare-rel f (Int Int))

(declare-var x Int)
(declare-var x1 Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=> (and
            (> x 0)
            (f x i)
          )
          (inv x i)))

(rule (=>
    (and
        (inv x i)
        (> x 0)
        (= x1 (- x 1))
        (= i1 (- i 1))
    )
    (inv x1 i1)
  )
)

(rule (=> (and (inv x i) (<= x 0) (not (= i 0))) fail))

(query fail)
