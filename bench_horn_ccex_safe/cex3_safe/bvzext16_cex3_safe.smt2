; SAFE zero-extend version of cex3: three variables x, y, z all increment by 1
; The transition only fires when ALL next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16)) Bool)

; Initial state: x = 0, y = 0, z = 0
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)) (z (_ BitVec 16)))
    (=> (and (= x #x0000) (= y #x0000) (= z #x0000)) (inv x y z))
  )
)

; Transition: all increment by 1, ONLY when all next states satisfy property
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)) (z (_ BitVec 16))
           (x_next (_ BitVec 16)) (y_next (_ BitVec 16)) (z_next (_ BitVec 16)))
    (=> (and (inv x y z)
             (bvult (bvadd ((_ zero_extend 16) x) #x00000002) #x00010000)
             (bvult (bvadd ((_ zero_extend 16) y) #x00000002) #x00010000)
             (bvult (bvadd ((_ zero_extend 16) z) #x00000002) #x00010000)
             (= x_next (bvadd x #x0001))
             (= y_next (bvadd y #x0001))
             (= z_next (bvadd z #x0001)))
        (inv x_next y_next z_next))
  )
)

; Property: all three must satisfy zext(v)+1 < 65536
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)) (z (_ BitVec 16)))
    (=> (and (inv x y z) 
             (not (and (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)
                       (bvult (bvadd ((_ zero_extend 16) y) #x00000001) #x00010000)
                       (bvult (bvadd ((_ zero_extend 16) z) #x00000001) #x00010000))))
        false)
  )
)

(check-sat)
