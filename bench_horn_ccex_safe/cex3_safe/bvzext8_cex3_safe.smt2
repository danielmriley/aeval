; SAFE zero-extend version of cex3: three variables x, y, z all increment by 1
; The transition only fires when ALL next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)

; Initial state: x = 0, y = 0, z = 0
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (z (_ BitVec 8)))
    (=> (and (= x #x00) (= y #x00) (= z #x00)) (inv x y z))
  )
)

; Transition: all increment by 1, ONLY when all next states satisfy property
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (z (_ BitVec 8))
           (x_next (_ BitVec 8)) (y_next (_ BitVec 8)) (z_next (_ BitVec 8)))
    (=> (and (inv x y z)
             (bvult (bvadd ((_ zero_extend 8) x) #x0002) #x0100)
             (bvult (bvadd ((_ zero_extend 8) y) #x0002) #x0100)
             (bvult (bvadd ((_ zero_extend 8) z) #x0002) #x0100)
             (= x_next (bvadd x #x01))
             (= y_next (bvadd y #x01))
             (= z_next (bvadd z #x01)))
        (inv x_next y_next z_next))
  )
)

; Property: all three must satisfy zext(v)+1 < 256
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (z (_ BitVec 8)))
    (=> (and (inv x y z) 
             (not (and (bvult (bvadd ((_ zero_extend 8) x) #x0001) #x0100)
                       (bvult (bvadd ((_ zero_extend 8) y) #x0001) #x0100)
                       (bvult (bvadd ((_ zero_extend 8) z) #x0001) #x0100))))
        false)
  )
)

(check-sat)
