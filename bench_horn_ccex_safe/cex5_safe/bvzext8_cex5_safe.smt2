; SAFE zero-extend version of cex5: x += 1, y += 2
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (= x #x00) (= y #x00)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2, ONLY when both next states satisfy property
; x' satisfies prop when zext(x)+2 < 256
; y' satisfies prop when zext(y)+4 < 256
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) 
           (x_next (_ BitVec 8)) (y_next (_ BitVec 8)))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend 8) x) #x0002) #x0100)
             (bvult (bvadd ((_ zero_extend 8) y) #x0004) #x0100)
             (= x_next (bvadd x #x01))
             (= y_next (bvadd y #x02)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 256 AND zext(y)+2 < 256
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 8) x) #x0001) #x0100)
                       (bvult (bvadd ((_ zero_extend 8) y) #x0002) #x0100))))
        false)
  )
)

(check-sat)
