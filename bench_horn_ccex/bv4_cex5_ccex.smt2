;; Compact CEX for bv4_cex5: x += 1, y += 2
;; x_at_i(i) = i
;; y_at_i(i) = 2*i
(define-fun x_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) i)
)
(define-fun y_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) (* 2 i))
)

(declare-const trace_x (Array Int (_ BitVec 4)))
(declare-const trace_y (Array Int (_ BitVec 4)))

(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 8)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)
(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 8)) 
        (= (select trace_y i) (y_at_i i))
    )
  )
)
