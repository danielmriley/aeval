; Zero-extend benchmark: 8-bit values, 16-bit counter
; Trace length: 257 steps (0 to 256)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 16)) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv #x00 #x0000)
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec 8)) (counter (_ BitVec 16)) 
           (x_next (_ BitVec 8)) (counter_next (_ BitVec 16)))
    (=> (and (inv x counter)
             (= x_next (bvadd x #x01))
             (= counter_next (bvadd counter ((_ zero_extend 8) #x01))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec 8)) (counter (_ BitVec 16)))
    (=> (inv x counter)
        (bvult counter #x0100))
  )
)

(check-sat)
