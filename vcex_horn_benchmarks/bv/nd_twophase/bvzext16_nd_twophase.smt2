; Two-phase CEX: x always increments, y increments only when x >= 32768
; Phase 1 (x < 32768): x++, y stays at 0
; Phase 2 (x >= 32768): x++, y++
; y reaches max after x does

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)))
    (=> (and (= x #x0000) (= y #x0000)) (inv x y))
  )
)

; Transition: x always increments, y increments only when x >= threshold
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)) 
           (x_next (_ BitVec 16)) (y_next (_ BitVec 16)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x0001))
             (ite (bvuge x #x8000)
                  (= y_next (bvadd y #x0001))
                  (= y_next y)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 65536 AND zext(y)+1 < 65536
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)
                       (bvult (bvadd ((_ zero_extend 16) y) #x00000001) #x00010000))))
        false)
  )
)

(check-sat)
