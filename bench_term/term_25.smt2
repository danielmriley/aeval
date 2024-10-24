(declare-rel inv (Int Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var w Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (=> (and (= w (+ x y z)) (= c 0)) (inv x y z w c)))

(rule (=> 
    (and 
        (inv x y z w c)
        (= w (+ x y z))
        (= y1 (ite (< c 100) (- y 1) y))
        (= c1 (+ c 1))
        (= x1 (+ x y1 c))
        (= z1 (- z y1))
    )
    (inv x1 y1 1 w c1)
  )
)
