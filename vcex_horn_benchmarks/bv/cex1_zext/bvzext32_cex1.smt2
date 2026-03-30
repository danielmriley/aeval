; Zero-extend version of cex1: single variable x, property uses zero_extend
; Equivalent to bv32_cex1.smt2 but with pure BV property (no bv2int)
;
; Original property: (not (< (+ 1 (bv2int x)) 2^32))
; With zero_extend: NOT(bvult(bvadd(zext(x), 1), 2^32))
;
; Trace: x=0,1,2,...,2^32-1 (2^32 states)

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (= x_next (bvadd x #x00000001)))
        (inv x_next))
  )
)

; Property: zero_extend(x) + 1 < 2^32 (violated when x = 2^32-1)
(assert 
  (forall ((x (_ BitVec 32)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000001) #x0000000100000000)))
        false)
  )
)

(check-sat)
