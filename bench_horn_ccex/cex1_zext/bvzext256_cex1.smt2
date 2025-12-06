; Zero-extend benchmark: 256-bit values, 512-bit counter
; Trace length: 2^256 + 1 steps (0 to 2^256)

(set-logic HORN)

(declare-fun inv ((_ BitVec 256) (_ BitVec 512)) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv #x0000000000000000000000000000000000000000000000000000000000000000 #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec 256)) (counter (_ BitVec 512)) 
           (x_next (_ BitVec 256)) (counter_next (_ BitVec 512)))
    (=> (and (inv x counter)
             (= x_next (bvadd x #x0000000000000000000000000000000000000000000000000000000000000001))
             (= counter_next (bvadd counter ((_ zero_extend 256) #x0000000000000000000000000000000000000000000000000000000000000001))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec 256)) (counter (_ BitVec 512)))
    (=> (inv x counter)
        (bvult counter #x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000))
  )
)

(check-sat)
