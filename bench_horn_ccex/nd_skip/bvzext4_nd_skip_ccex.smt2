; CCEX for nd_skip: explicit path with +1 and +3 steps
; Path: [0, 1, 4, 5, 8, 9, 12, 13, 14, 15]
; Steps: +1, +3, +1, +3, +1, +3, +1, +1, +1
; Total steps: 9, final value: 15
; Trace bounds: 0 to 9

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  (ite (= i #x09) #xf
    (ite (= i #x08) #xe
    (ite (= i #x07) #xd
    (ite (= i #x06) #xc
    (ite (= i #x05) #x9
    (ite (= i #x04) #x8
    (ite (= i #x03) #x5
    (ite (= i #x02) #x4
    (ite (= i #x01) #x1
    #x0)))))))))
)

(declare-const trace (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x09)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
