; Quadratic Growth (Accumulator)
; x starts at 0, increments by 1
; y starts at 0, accumulates x
; Property: 2y = x(x-1)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (inv #x0 #x0)
)

; Transition: x' = x + 1, y' = y + x
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)) (x_next (_ BitVec 4)) (y_next (_ BitVec 4)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x1))
             (= y_next (bvadd y x)))
        (inv x_next y_next))
  )
)

; Property: y != 12
; Negation: y = 12
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
    (=> (and (inv x y) 
             (= y #xC))
        false)
  )
)

(check-sat)
