; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 2

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((n (_ BitVec 8))) (_ BitVec 16) ((_ zero_extend 8) n))
(define-fun var_1_at_i ((n (_ BitVec 8))) (_ BitVec 16) (let ((_let_1 ((_ zero_extend 8) n))) (bvmul _let_1 _let_1)))

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 8) (_ BitVec 16)))
(declare-const trace_1 (Array (_ BitVec 8) (_ BitVec 16)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 8)))
    (=> (and (bvule #x00 i) (bvule i #xff))
        (and
          (= (select trace_0 i) (var_0_at_i i))
          (= (select trace_1 i) (var_1_at_i i))
        )
    )
  )
)

(check-sat)
