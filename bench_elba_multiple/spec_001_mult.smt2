(declare-rel itp1 (Int Int Int Int Int Int))
(declare-rel itp2 (Int Int Int Int Int Int))
(declare-rel itp3 (Int Int Int Int Int Int))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y1 Int)
(declare-var y2 Int)
(declare-var z1 Int)
(declare-var z2 Int)
(declare-var n Int)
(declare-var m Int)
(declare-var o Int)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= y1 0) (= z1 0)) (itp1 x1 y1 z1 n m o)))

(rule (=>
    (and
      (itp1 x1 y1 z1 n m o)
      (< x1 n)
      (= x2 (+ x1 1))
      (= y2 y1)
      (= z2 z1)
    )
    (itp1 x2 y2 z2 n m o)
  )
)

(rule (=> (itp1 x1 y1 z1 n m o) (itp2 x1 y1 z1 n m o)))

(rule (=>
    (and
      (itp2 x1 y1 z1 n m o)
      (< y1 m)
      (= y2 (+ y1 1))
      (= x2 x1)
      (= z2 z1)
    )
    (itp2 x2 y2 z2 n m o)
  )
)

(rule (=> (itp2 x1 y1 z1 n m o) (itp3 x1 y1 z1 n m o)))

(rule (=>
    (and
      (itp3 x1 y1 z1 n m o)
      (< z1 o)
      (= z2 (+ z1 1))
      (= x2 x1)
      (= y2 y1)
    )
    (itp3 x2 y2 z2 n m o)
  )
)
