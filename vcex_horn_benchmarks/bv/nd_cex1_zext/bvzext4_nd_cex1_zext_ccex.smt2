; CCEX for nd_cex1_zext: x increments, y stays at 0
; This represents the path where we always choose to increment x
; x goes 0,1,2,...,15 while y stays at 0
; Error occurs when x overflows (x = 15, zext(x)+1 >= 2^k)
; Trace bounds: 0 to 15

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) i)
)

(define-fun y_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  #x0
)

(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 4)))
(declare-const trace_y (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x0f)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
