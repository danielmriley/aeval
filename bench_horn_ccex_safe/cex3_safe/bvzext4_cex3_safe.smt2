; SAFE zero-extend version of cex3: three variables x, y, z all increment by 1
; The transition only fires when ALL next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4)) Bool)

; Initial state: x = 0, y = 0, z = 0
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)) (z (_ BitVec 4)))
    (=> (and (= x #x0) (= y #x0) (= z #x0)) (inv x y z))
  )
)

; Transition: all increment by 1, ONLY when all next states satisfy property
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)) (z (_ BitVec 4))
           (x_next (_ BitVec 4)) (y_next (_ BitVec 4)) (z_next (_ BitVec 4)))
    (=> (and (inv x y z)
             (bvult (bvadd ((_ zero_extend 4) x) #x02) #x10)
             (bvult (bvadd ((_ zero_extend 4) y) #x02) #x10)
             (bvult (bvadd ((_ zero_extend 4) z) #x02) #x10)
             (= x_next (bvadd x #x1))
             (= y_next (bvadd y #x1))
             (= z_next (bvadd z #x1)))
        (inv x_next y_next z_next))
  )
)

; Property: all three must satisfy zext(v)+1 < 16
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)) (z (_ BitVec 4)))
    (=> (and (inv x y z) 
             (not (and (bvult (bvadd ((_ zero_extend 4) x) #x01) #x10)
                       (bvult (bvadd ((_ zero_extend 4) y) #x01) #x10)
                       (bvult (bvadd ((_ zero_extend 4) z) #x01) #x10))))
        false)
  )
)

(check-sat)
