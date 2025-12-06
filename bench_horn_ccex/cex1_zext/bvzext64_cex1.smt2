; Zero-extend benchmark: 64-bit values, 128-bit counter
; Trace length: 18446744073709551617 steps (0 to 18446744073709551616)

(set-logic HORN)

(declare-fun inv ((_ BitVec 64) (_ BitVec 128)) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv #x0000000000000000 #x00000000000000000000000000000000)
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec 64)) (counter (_ BitVec 128)) 
           (x_next (_ BitVec 64)) (counter_next (_ BitVec 128)))
    (=> (and (inv x counter)
             (= x_next (bvadd x #x0000000000000001))
             (= counter_next (bvadd counter ((_ zero_extend 64) #x0000000000000001))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec 64)) (counter (_ BitVec 128)))
    (=> (inv x counter)
        (bvult counter #x00000000000000010000000000000000))
  )
)

(check-sat)
