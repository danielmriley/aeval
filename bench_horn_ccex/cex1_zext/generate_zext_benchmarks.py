#!/usr/bin/env python3
"""
Generate zero-extend benchmarks for various bit widths.
These benchmarks use a counter with 2x the bit width to avoid int2bv issues.
"""

import os

def generate_chc(k):
    """Generate CHC file for k-bit zero-extend benchmark."""
    counter_bits = 2 * k
    max_val = 2**k  # Counter reaches this value when overflow would occur
    
    # Format hex values appropriately
    def hex_val(val, bits):
        hex_digits = (bits + 3) // 4
        return f"#x{val:0{hex_digits}x}"
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    counter_zero = hex_val(0, counter_bits)
    counter_one = hex_val(1, k)  # For zero_extend source
    counter_max = hex_val(max_val, counter_bits)
    
    # For comments, use 2^k notation for large values
    if k <= 64:
        trace_len_str = f"{max_val + 1} steps (0 to {max_val})"
    else:
        trace_len_str = f"2^{k} + 1 steps (0 to 2^{k})"
    
    return f"""; Zero-extend benchmark: {k}-bit values, {counter_bits}-bit counter
; Trace length: {trace_len_str}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {counter_bits})) Bool)

; Initial state: x = 0, counter = 0
(assert 
  (inv {x_zero} {counter_zero})
)

; Transition: x' = x + 1, counter' = counter + zero_extend(1)
(assert 
  (forall ((x (_ BitVec {k})) (counter (_ BitVec {counter_bits})) 
           (x_next (_ BitVec {k})) (counter_next (_ BitVec {counter_bits})))
    (=> (and (inv x counter)
             (= x_next (bvadd x {x_one}))
             (= counter_next (bvadd counter ((_ zero_extend {k}) {counter_one}))))
        (inv x_next counter_next))
  )
)

; Property: counter < 2^k (should be violated after 2^k steps)
(assert 
  (forall ((x (_ BitVec {k})) (counter (_ BitVec {counter_bits})))
    (=> (inv x counter)
        (bvult counter {counter_max}))
  )
)

(check-sat)
"""

def generate_ccex(k):
    """Generate CCEX file for k-bit zero-extend benchmark."""
    counter_bits = 2 * k
    max_val = 2**k
    
    # Format hex values
    def hex_val(val, bits):
        hex_digits = (bits + 3) // 4
        return f"#x{val:0{hex_digits}x}"
    
    counter_zero = hex_val(0, counter_bits)
    counter_max = hex_val(max_val, counter_bits)
    
    # For comments, use 2^k notation for large values
    if k <= 64:
        bounds_str = f"0 to {max_val}"
    else:
        bounds_str = f"0 to 2^{k}"
    
    return f"""; Compact CEX for {k}-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower {k} bits from {counter_bits}-bit index
;   counter at step i = i (the index itself)
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {counter_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun counter_at_i ((i (_ BitVec {counter_bits}))) (_ BitVec {counter_bits})
  i
)

(declare-const trace_x (Array (_ BitVec {counter_bits}) (_ BitVec {k})))
(declare-const trace_counter (Array (_ BitVec {counter_bits}) (_ BitVec {counter_bits})))

(assert 
  (forall ((i (_ BitVec {counter_bits}))) 
    (=> (and (bvule {counter_zero} i) (bvule i {counter_max})) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
"""

def main():
    # Generate benchmarks for powers of 2 from 4 to 65536
    bit_widths = [4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]
    
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    for k in bit_widths:
        # Generate CHC file
        chc_filename = f"bvzext{k}_cex1.smt2"
        chc_path = os.path.join(script_dir, chc_filename)
        with open(chc_path, 'w') as f:
            f.write(generate_chc(k))
        print(f"Generated {chc_filename}")
        
        # Generate CCEX file
        ccex_filename = f"bvzext{k}_cex1_ccex.smt2"
        ccex_path = os.path.join(script_dir, ccex_filename)
        with open(ccex_path, 'w') as f:
            f.write(generate_ccex(k))
        print(f"Generated {ccex_filename}")

if __name__ == "__main__":
    main()
