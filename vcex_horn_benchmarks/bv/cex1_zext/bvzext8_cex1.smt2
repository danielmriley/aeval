; Zero-extend version of cex1: single variable x, property uses zero_extend
; Equivalent to bv8_cex1.smt2 but with pure BV property (no bv2int)
;
; Original property: (not (< (+ 1 (bv2int x)) 256))
; With zero_extend: NOT(bvult(bvadd(zext(x), 1), 256))
;
; Trace: x=0,1,2,...,255 (256 states)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (= x_next (bvadd x #x01)))
        (inv x_next))
  )
)

; Property: zero_extend(x) + 1 < 256 (violated when x = 255)
(assert 
  (forall ((x (_ BitVec 8)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 8) x) #x0001) #x0100)))
        false)
  )
)

(check-sat)
