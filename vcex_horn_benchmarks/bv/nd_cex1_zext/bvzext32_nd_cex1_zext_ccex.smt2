; CCEX for nd_cex1_zext: x increments, y stays at 0
; This represents the path where we always choose to increment x
; x goes 0,1,2,...,4294967295 while y stays at 0
; Error occurs when x overflows (x = 4294967295, zext(x)+1 >= 2^k)
; Trace bounds: 0 to 4294967295

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(define-fun y_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  #x00000000
)

(declare-const trace_x (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const trace_y (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x00000000ffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
