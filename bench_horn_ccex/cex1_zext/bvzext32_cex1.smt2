; Zero-extend benchmark: 32-bit values, 64-bit counter
; Trace length: 4294967297 steps (0 to 4294967296)

(set-logic HORN)

(declare-fun inv ((_ BitVec 32) (_ BitVec 64)) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv #x00000000 #x0000000000000000)
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec 32)) (counter (_ BitVec 64)) 
           (x_next (_ BitVec 32)) (counter_next (_ BitVec 64)))
    (=> (and (inv x counter)
             (= x_next (bvadd x #x00000001))
             (= counter_next (bvadd counter ((_ zero_extend 32) #x00000001))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec 32)) (counter (_ BitVec 64)))
    (=> (inv x counter)
        (bvult counter #x0000000100000000))
  )
)

(check-sat)
