#!/usr/bin/env python3
"""Generate zero-extend benchmarks for various bitwidths.

These benchmarks use zero_extend instead of bv2int/int2bv to avoid
solver performance issues with bounded int2bv formulas.

For a k-bit system:
- x is k bits, increments from 0
- counter is 2k bits, tracks iterations using zero_extend
- property: counter >= 2^k (i.e., x has wrapped around)
"""

import os

def hex_val(value, bits):
    """Format value as hex with appropriate width."""
    hex_chars = (bits + 3) // 4
    return f"#x{value:0{hex_chars}x}"

def generate_cex(k):
    """Generate CHC file for k-bit benchmark."""
    k2 = 2 * k  # counter bitwidth
    max_val = 2**k  # counter target (trace length)
    
    return f"""; Zero-extend benchmark: {k}-bit values, {k2}-bit counter
; Trace length: {max_val + 1} steps (0 to {max_val})

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k2})) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv {hex_val(0, k)} {hex_val(0, k2)})
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec {k})) (counter (_ BitVec {k2})) 
           (x_next (_ BitVec {k})) (counter_next (_ BitVec {k2})))
    (=> (and (inv x counter)
             (= x_next (bvadd x {hex_val(1, k)}))
             (= counter_next (bvadd counter ((_ zero_extend {k}) {hex_val(1, k)}))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec {k})) (counter (_ BitVec {k2})))
    (=> (inv x counter)
        (bvult counter {hex_val(max_val, k2)}))
  )
)

(check-sat)
"""

def generate_ccex(k):
    """Generate CCEX file for k-bit benchmark."""
    k2 = 2 * k
    max_val = 2**k
    
    return f"""; Compact CEX for {k}-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower {k} bits from {k2}-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to {max_val}

(define-fun x_at_i ((i (_ BitVec {k2}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun counter_at_i ((i (_ BitVec {k2}))) (_ BitVec {k2})
  i
)

(declare-const trace_x (Array (_ BitVec {k2}) (_ BitVec {k})))
(declare-const trace_counter (Array (_ BitVec {k2}) (_ BitVec {k2})))

(assert 
  (forall ((i (_ BitVec {k2}))) 
    (=> (and (bvule {hex_val(0, k2)} i) (bvule i {hex_val(max_val, k2)})) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
"""

def main():
    # Bitwidths to generate
    bitwidths = [4, 8, 16, 32, 64, 128, 256, 512]
    
    output_dir = os.path.dirname(os.path.abspath(__file__))
    
    for k in bitwidths:
        # Generate CHC file
        cex_file = os.path.join(output_dir, f"bvzext{k}_cex1.smt2")
        with open(cex_file, 'w') as f:
            f.write(generate_cex(k))
        print(f"Generated {cex_file}")
        
        # Generate CCEX file
        ccex_file = os.path.join(output_dir, f"bvzext{k}_cex1_ccex.smt2")
        with open(ccex_file, 'w') as f:
            f.write(generate_ccex(k))
        print(f"Generated {ccex_file}")

if __name__ == "__main__":
    main()
