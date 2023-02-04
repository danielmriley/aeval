(declare-rel itp1 (Int Int))
(declare-rel itp2 (Int Int))
(declare-rel itp3 (Int Int))

(declare-var x1 Int)
(declare-var y1 Int)
(declare-var x2 Int)
(declare-var y2 Int)

(declare-rel fail ())

(rule (=> true (itp1 x1 y1)))

(rule (=>
    (and
      (itp1 x1 y1)
      (> x1 0)
      (> y1 0)
      (= x2 (- x1 1))
      (= y2 (- y1 1))
    )
    (itp1 x2 y2)
  )
)

(rule (=> (and (not (and (> x1 0) (> y1 0))) (itp1 x1 y1)) (itp2 x1 y1)))

(rule (=>
    (and
      (itp2 x1 y1)
      (> y1 0)
      (= y2 (- y1 1))
    )
    (itp2 x1 y2)
  )
)

(rule (=> (and (<= y1 0) (itp2 x1 y1)) (itp3 x1 y1)))

(rule (=>
    (and
      (itp3 x1 y1)
      (> x1 0)
      (= x2 (- x1 1))
    )
    (itp3 x2 y1)
  )
)
