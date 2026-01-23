; CCEX file for s_split_05 with correct closed-forms
; x(n) = n + 1
; y(n) = 2*n - 1  
; z(n) = (n < 1) ? 1 : (1 << (n - 1))

(define-fun var_0_at_i ((i (_ BitVec 8))) (_ BitVec 16)
  (bvadd ((_ zero_extend 8) i) #x0001))

(define-fun var_1_at_i ((i (_ BitVec 8))) (_ BitVec 16)
  (bvsub (bvadd ((_ zero_extend 8) i) ((_ zero_extend 8) i)) #x0001))

(define-fun var_2_at_i ((i (_ BitVec 8))) (_ BitVec 16)
  (ite (bvult ((_ zero_extend 8) i) #x0001) 
       #x0001 
       (bvshl #x0001 (bvsub ((_ zero_extend 8) i) #x0001))))

; Trace arrays
(declare-const trace_0 (Array (_ BitVec 8) (_ BitVec 16)))
(declare-const trace_1 (Array (_ BitVec 8) (_ BitVec 16)))
(declare-const trace_2 (Array (_ BitVec 8) (_ BitVec 16)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 8)))
    (=> (and (bvule #x00 i) (bvule i #xff))
        (and
          (= (select trace_0 i) (var_0_at_i i))
          (= (select trace_1 i) (var_1_at_i i))
          (= (select trace_2 i) (var_2_at_i i))
        )
    )
  )
)

(check-sat)
