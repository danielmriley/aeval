; Zero-extend version of cex1: single variable x, property uses zero_extend
; Equivalent to bv4_cex1.smt2 but with pure BV property (no bv2int)
;
; Original property: (not (< (+ 1 (bv2int x)) 16))
; With zero_extend: NOT(bvult(bvadd(zext(x), 1), 16))
;
; Trace: x=0,1,2,...,15 (16 states)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (= x_next (bvadd x #x1)))
        (inv x_next))
  )
)

; Property: zero_extend(x) + 1 < 16 (violated when x = 15)
(assert 
  (forall ((x (_ BitVec 4)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 4) x) #x01) #x10)))
        false)
  )
)
(check-sat)
