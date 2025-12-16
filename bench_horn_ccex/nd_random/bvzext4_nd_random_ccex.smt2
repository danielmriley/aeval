; CCEX for nd_random: explicit enumeration of random path
; This is NOT a closed-form function - it enumerates each step explicitly
; Values: [0, 10, 1, 0, 11, 4, 3, 3, 2, 11, 1, 10, 11, 14, 8, 15]
; Trace bounds: 0 to 15

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  (ite (= i #x0f) #xf
    (ite (= i #x0e) #x8
    (ite (= i #x0d) #xe
    (ite (= i #x0c) #xb
    (ite (= i #x0b) #xa
    (ite (= i #x0a) #x1
    (ite (= i #x09) #xb
    (ite (= i #x08) #x2
    (ite (= i #x07) #x3
    (ite (= i #x06) #x3
    (ite (= i #x05) #x4
    (ite (= i #x04) #xb
    (ite (= i #x03) #x0
    (ite (= i #x02) #x1
    (ite (= i #x01) #xa
    #x0)))))))))))))))
)

(declare-const trace (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x0f)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
