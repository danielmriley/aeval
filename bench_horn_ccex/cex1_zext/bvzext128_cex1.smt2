; Zero-extend version of cex1: single variable x, property uses zero_extend
; Equivalent to bv128_cex1.smt2 but with pure BV property (no bv2int)
;
; Original property: (not (< (+ 1 (bv2int x)) 2^128))
; With zero_extend: NOT(bvult(bvadd(zext(x), 1), 2^128))
;
; Trace: x=0,1,2,...,2^128-1 (2^128 states)

(set-logic HORN)

(declare-fun inv ((_ BitVec 128)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000000000000000000000000000)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 128)) (x_next (_ BitVec 128)))
    (=> (and (inv x)
             (= x_next (bvadd x #x00000000000000000000000000000001)))
        (inv x_next))
  )
)

; Property: zero_extend(x) + 1 < 2^128 (violated when x = 2^128-1)
(assert 
  (forall ((x (_ BitVec 128)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000001) #x0000000000000000000000000000000100000000000000000000000000000000)))
        false)
  )
)

(check-sat)
