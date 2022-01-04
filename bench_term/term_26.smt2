(declare-rel inv ( Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)

(rule (inv x y 0 0))

(rule (=> 
    (and 
        (inv x y a b)
        (= x y)
        (= x1 (+ x (mod a 2)))
        (= y1 (+ y (mod b 3)))
        (= a1 (+ a 1))
        (= b1 (+ b 1))
    )
    (inv x1 y1 a1 b1)
  )
)
