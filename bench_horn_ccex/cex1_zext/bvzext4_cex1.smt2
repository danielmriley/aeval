; Zero-extend benchmark: 4-bit values, 8-bit counter
; Trace length: 17 steps (0 to 16)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4) (_ BitVec 8)) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv #x0 #x00)
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec 4)) (counter (_ BitVec 8)) 
           (x_next (_ BitVec 4)) (counter_next (_ BitVec 8)))
    (=> (and (inv x counter)
             (= x_next (bvadd x #x1))
             (= counter_next (bvadd counter ((_ zero_extend 4) #x1))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec 4)) (counter (_ BitVec 8)))
    (=> (inv x counter)
        (bvult counter #x10))
  )
)

(check-sat)
