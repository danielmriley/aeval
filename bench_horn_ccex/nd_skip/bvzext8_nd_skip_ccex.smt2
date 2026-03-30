; CCEX for nd_skip k=8: shortest path using all +3 steps
; x(0) = 0, x(i) = 3*i (mod 2^8)
; Reaches 255 in exactly 85 steps (255 = 85 * 3)
; Trace bounds: 0 to 85 (= (2^8 - 1) / 3 = 0x55)

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  (bvmul ((_ extract 7 0) i) #x03)
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 8)))

(assert
  (forall ((i (_ BitVec 16)))
    (=> (and (bvule #x0000 i) (bvule i #x0055))
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
