; Zero-extend benchmark: 16-bit values, 32-bit counter
; Trace length: 65537 steps (0 to 65536)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 32)) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv #x0000 #x00000000)
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec 16)) (counter (_ BitVec 32)) 
           (x_next (_ BitVec 16)) (counter_next (_ BitVec 32)))
    (=> (and (inv x counter)
             (= x_next (bvadd x #x0001))
             (= counter_next (bvadd counter ((_ zero_extend 16) #x0001))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec 16)) (counter (_ BitVec 32)))
    (=> (inv x counter)
        (bvult counter #x00010000))
  )
)

(check-sat)
