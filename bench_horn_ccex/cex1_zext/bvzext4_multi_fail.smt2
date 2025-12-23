(set-logic HORN)
(declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)

; Initial: x=0, y=0
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) 
  (=> (and (= x #x0) (= y #x0)) (inv x y))))

; Trans: x' = x+1, y' = y+1
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4)) (xn (_ BitVec 4)) (yn (_ BitVec 4)))
    (=> (and (inv x y) (= xn (bvadd x #x1)) (= yn (bvadd y #x1))) (inv xn yn))))

; Property: x < 1 AND y < 1
; Step 0: x=0, y=0 (Pass)
; Step 1: x=1, y=1 (Fail: both x>=1 and y>=1)
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
    (=> (and (inv x y) 
             (not (and (bvult x #x1) (bvult y #x1)))) 
        false)))
(check-sat)
