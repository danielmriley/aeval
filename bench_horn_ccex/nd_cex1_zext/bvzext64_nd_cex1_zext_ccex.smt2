; CCEX for nd_cex1_zext: x increments, y stays at 0
; This represents the path where we always choose to increment x
; x goes 0,1,2,...,18446744073709551615 while y stays at 0
; Error occurs when x overflows (x = 18446744073709551615, zext(x)+1 >= 2^k)
; Trace bounds: 0 to 18446744073709551615

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) i)
)

(define-fun y_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  #x0000000000000000
)

(declare-const trace_x (Array (_ BitVec 128) (_ BitVec 64)))
(declare-const trace_y (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x0000000000000000ffffffffffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
