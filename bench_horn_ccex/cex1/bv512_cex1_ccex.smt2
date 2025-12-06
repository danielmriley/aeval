(define-fun x_at_i ((i Int)) (_ BitVec 512)
  ((_ int2bv 512) i)
)

(declare-const trace (Array Int (_ BitVec 512)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
