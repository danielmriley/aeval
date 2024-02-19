(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (inv 0))

(rule (=>
    (and
        (inv x)
        (< x 2)
        (= x1 (+ x 1))
    )
    (inv x1)
  )
)

(rule (=> (and (inv x) (not (< x 2)) ) fail))

(query fail :print-certificate true)
