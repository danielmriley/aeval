; Nondeterministic CEX: x++ OR y++ (not both) - zext version
; At each step, EITHER x increments by 1 OR y increments by 1
; Error when either variable overflows
; This creates exponentially many paths but a simple CCEX where x=y=i works

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (= x #x00) (= y #x00)) (inv x y))
  )
)

; Transition: EITHER x' = x + 1 (y unchanged) OR y' = y + 1 (x unchanged)
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) 
           (x_next (_ BitVec 8)) (y_next (_ BitVec 8)))
    (=> (and (inv x y)
             (or (and (= x_next (bvadd x #x01)) (= y_next y))
                 (and (= x_next x) (= y_next (bvadd y #x01)))))
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
