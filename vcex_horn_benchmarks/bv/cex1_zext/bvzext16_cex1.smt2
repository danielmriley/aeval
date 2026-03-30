; Zero-extend version of cex1: single variable x, property uses zero_extend
; Equivalent to bv16_cex1.smt2 but with pure BV property (no bv2int)
;
; Original property: (not (< (+ 1 (bv2int x)) 65536))
; With zero_extend: NOT(bvult(bvadd(zext(x), 1), 65536))
;
; Trace: x=0,1,2,...,65535 (65536 states)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x)
             (= x_next (bvadd x #x0001)))
        (inv x_next))
  )
)

; Property: zero_extend(x) + 1 < 65536 (violated when x = 65535)
(assert 
  (forall ((x (_ BitVec 16)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)))
        false)
  )
)

(check-sat)
