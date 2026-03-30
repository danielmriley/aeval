; Zero-extend version of cex3: three variables x, y, z all increment by 1
; Property: zext(x)+1 < 256 AND zext(y)+1 < 256 AND zext(z)+1 < 256
; Trace: 0 to 255

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)

; Initial state: x = 0, y = 0, z = 0
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (z (_ BitVec 8)))
    (=> (and (= x #x00) (= y #x00) (= z #x00)) (inv x y z))
  )
)

; Transition: x' = x + 1, y' = y + 1, z' = z + 1
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (z (_ BitVec 8))
           (x_next (_ BitVec 8)) (y_next (_ BitVec 8)) (z_next (_ BitVec 8)))
    (=> (and (inv x y z)
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
