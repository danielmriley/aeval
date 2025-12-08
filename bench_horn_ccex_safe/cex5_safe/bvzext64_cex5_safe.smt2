; SAFE zero-extend version of cex5: x += 1, y += 2
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
    (=> (and (= x #x0000000000000000) (= y #x0000000000000000)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2, ONLY when both next states satisfy property
; x' satisfies prop when zext(x)+2 < 2^64
; y' satisfies prop when zext(y)+4 < 2^64
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) 
           (x_next (_ BitVec 64)) (y_next (_ BitVec 64)))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend 64) x) #x00000000000000000000000000000002) #x00000000000000010000000000000000)
             (bvult (bvadd ((_ zero_extend 64) y) #x00000000000000000000000000000004) #x00000000000000010000000000000000)
             (= x_next (bvadd x #x0000000000000001))
             (= y_next (bvadd y #x0000000000000002)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 2^64 AND zext(y)+2 < 2^64
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 64) x) #x00000000000000000000000000000001) #x00000000000000010000000000000000)
                       (bvult (bvadd ((_ zero_extend 64) y) #x00000000000000000000000000000002) #x00000000000000010000000000000000))))
        false)
  )
)

(check-sat)
