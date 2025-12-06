;; Compact CEX for bv4_cex4: x increments by 2 each step
;; x_at_i(i) = 2*i (mod 16)
(define-fun x_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) (* 2 i))
)

(declare-const trace (Array Int (_ BitVec 4)))

(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 8)) 
        (= (select trace i) (x_at_i i))
    )
  )
)
