;; Example 4: Single variable incrementing by 2 each iteration
;; x starts at 0, increments by 2: 0, 2, 4, 6, 8, 10, 12, 14, 0 (overflow), ...
;; Reaches overflow after 8 iterations
(declare-fun inv ((_ BitVec 4)) Bool)

(assert (forall ((x (_ BitVec 4))) 
  (=> (= x #b0000) (inv x))
))
(assert (forall ((x0 (_ BitVec 4)) (x1 (_ BitVec 4))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #b0010)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 4))) 
  (=> (and (inv x) (not (< (+ 2 (bv2int x)) 16))) false)
))

(check-sat)
