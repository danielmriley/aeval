;; Compact CEX for bv4_cex6: x starts at 5, increments by 1
;; x_at_i(i) = 5 + i
(define-fun x_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) (+ 5 i))
)

(declare-const trace (Array Int (_ BitVec 4)))

(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 11)) 
        (= (select trace i) (x_at_i i))
    )
  )
)
