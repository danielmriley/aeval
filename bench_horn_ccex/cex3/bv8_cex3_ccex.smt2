; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 3

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((n (_ BitVec 8))) (_ BitVec 8) n)
(define-fun var_1_at_i ((n (_ BitVec 8))) (_ BitVec 8) n)
(define-fun var_2_at_i ((n (_ BitVec 8))) (_ BitVec 8) n)

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const trace_1 (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const trace_2 (Array (_ BitVec 8) (_ BitVec 8)))

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
