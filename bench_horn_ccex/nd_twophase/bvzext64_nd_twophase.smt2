; Two-phase CEX: x always increments, y increments only when x >= 2^63
; Phase 1 (x < 2^63): x++, y stays at 0
; Phase 2 (x >= 2^63): x++, y++
; y reaches max after x does

(set-logic HORN)

(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
    (=> (and (= x #x0000000000000000) (= y #x0000000000000000)) (inv x y))
  )
)

; Transition: x always increments, y increments only when x >= threshold
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) 
           (x_next (_ BitVec 64)) (y_next (_ BitVec 64)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x0000000000000001))
             (ite (bvuge x #x8000000000000000)
                  (= y_next (bvadd y #x0000000000000001))
                  (= y_next y)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 2^64 AND zext(y)+1 < 2^64
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 64) x) #x00000000000000000000000000000001) #x00000000000000010000000000000000)
                       (bvult (bvadd ((_ zero_extend 64) y) #x00000000000000000000000000000001) #x00000000000000010000000000000000))))
        false)
  )
)

(check-sat)
