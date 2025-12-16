; CCEX for nd_cex1_zext: x increments, y stays at 0
; This represents the path where we always choose to increment x
; x goes 0,1,2,...,255 while y stays at 0
; Error occurs when x overflows (x = 255, zext(x)+1 >= 2^k)
; Trace bounds: 0 to 255

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(define-fun y_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  #x00
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 8)))
(declare-const trace_y (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
