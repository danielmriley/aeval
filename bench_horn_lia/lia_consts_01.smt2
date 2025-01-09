(declare-rel inv ((Int)))
(declare-var a (Int))
(declare-var a1 (Int))

(declare-rel fail ())

(rule (=> (and (= a 0)) (inv a)))

(rule (=> (and 
  (inv a)
  (< a 254)
  (= a1 (+ a 1)))
  (inv a1)))

(rule (=> (and (inv a) (>= a 255)) fail))

(query fail :print-certificate true)

