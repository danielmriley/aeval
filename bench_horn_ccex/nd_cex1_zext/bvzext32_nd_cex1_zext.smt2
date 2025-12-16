; Nondeterministic CEX: x++ OR y++ (not both) - zext version
; At each step, EITHER x increments by 1 OR y increments by 1
; Error when either variable overflows
; This creates exponentially many paths but a simple CCEX where x=y=i works

(set-logic HORN)

(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
    (=> (and (= x #x00000000) (= y #x00000000)) (inv x y))
  )
)

; Transition: EITHER x' = x + 1 (y unchanged) OR y' = y + 1 (x unchanged)
(assert 
  (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) 
           (x_next (_ BitVec 32)) (y_next (_ BitVec 32)))
    (=> (and (inv x y)
             (or (and (= x_next (bvadd x #x00000001)) (= y_next y))
                 (and (= x_next x) (= y_next (bvadd y #x00000001)))))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 2^32 AND zext(y)+1 < 2^32
(assert 
  (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000001) #x0000000100000000)
                       (bvult (bvadd ((_ zero_extend 32) y) #x0000000000000001) #x0000000100000000))))
        false)
  )
)

(check-sat)
