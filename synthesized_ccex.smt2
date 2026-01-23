; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 2

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((n (_ BitVec 16))) (_ BitVec 16) n)
(define-fun var_1_at_i ((n (_ BitVec 16))) (_ BitVec 16) (ite (bvult n #b0000011111010000) #b0000011111010000 n))

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_1 (Array (_ BitVec 16) (_ BitVec 16)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 16)))
    (=> (and (bvule #x0000 i) (bvule i #x0fa0))
        (and
          (= (select trace_0 i) (var_0_at_i i))
          (= (select trace_1 i) (var_1_at_i i))
        )
    )
  )
)

(check-sat)
