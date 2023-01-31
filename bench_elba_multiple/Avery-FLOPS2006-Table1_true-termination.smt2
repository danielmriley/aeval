(declare-rel itp1 (Int Int Int Int))
(declare-rel itp2 (Int Int Int Int))
(declare-rel itp3 (Int Int Int Int))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y1 Int)
(declare-var y2 Int)
(declare-var z1 Int)
(declare-var z2 Int)
(declare-var i1 Int)
(declare-var i2 Int)

(declare-rel fail ())

(rule (=> (and (> x1 0) (> y1 0) (= i1 x1) (= z1 0)) (itp1 x1 y1 z1 i1)))

(rule (=>
    (and
      (itp1 x1 y1 z1 i1)
      (> i1 0)
      (= i2 (- i1 1))
      (= y2 y1)
      (= x2 x1)
      (= z2 (+ z1 1))
    )
    (itp1 x2 y2 z2 i2)
  )
)

(rule (=> (itp1 x1 y1 z1 i1) (itp2 x1 y1 z1 i1)))

(rule (=>
    (and
      (itp2 x1 y1 z1 i1)
      (< i1 y1)
      (= i2 (+ i1 1))
      (= x2 x1)
      (= y2 y1)
      (= z2 (- z1 1))
    )
    (itp2 x2 y2 z2 i2)
  )
)
