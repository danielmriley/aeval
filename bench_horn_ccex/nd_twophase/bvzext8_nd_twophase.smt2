; Two-phase CEX: x always increments, y increments only when x >= 128
; Phase 1 (x < 128): x++, y stays at 0
; Phase 2 (x >= 128): x++, y++
; y reaches max after x does

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (= x #x00) (= y #x00)) (inv x y))
  )
)

; Transition: x always increments, y increments only when x >= threshold
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) 
           (x_next (_ BitVec 8)) (y_next (_ BitVec 8)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x01))
             (ite (bvuge x #x80)
                  (= y_next (bvadd y #x01))
                  (= y_next y)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 256 AND zext(y)+1 < 256
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 8) x) #x0001) #x0100)
                       (bvult (bvadd ((_ zero_extend 8) y) #x0001) #x0100))))
        false)
  )
)

(check-sat)
