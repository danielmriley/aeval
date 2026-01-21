; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 3

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((i (_ BitVec 16))) (_ BitVec 16) i)
(define-fun var_1_at_i ((i (_ BitVec 16))) (_ BitVec 16) #b0000000000000000)
(define-fun var_2_at_i ((i (_ BitVec 16))) (_ BitVec 16) i)

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_1 (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_2 (Array (_ BitVec 16) (_ BitVec 16)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 16)))
    (=> (and (bvule #x0000 i) (bvule i #xffff))
        (and
          (= (select trace_0 i) (var_0_at_i i))
          (= (select trace_1 i) (var_1_at_i i))
          (= (select trace_2 i) (var_2_at_i i))
        )
    )
  )
)

(check-sat)
