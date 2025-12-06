#!/usr/bin/env python3
"""
Generate zero-extend benchmarks for various bit widths.
These are equivalent to cex1 benchmarks but with pure BV property (no bv2int).

CHC structure: Single variable x (k bits)
- Init: x = 0
- Trans: x' = x + 1
- Property: zero_extend(x) + 1 < 2^k (violated when x = 2^k - 1)

CCEX structure: 
- Index is 2k-bit BV (replaces Int index from original)
- Value function: x_at_i(i) = extract(i) (lower k bits)
- Bounds: 0 to 2^k - 1
"""

import os

def generate_chc(k):
    """Generate CHC file for k-bit zero-extend benchmark."""
    index_bits = 2 * k  # Index type is 2x width for overflow-free counting
    
    # Format hex values appropriately
    def hex_val(val, bits):
        hex_digits = (bits + 3) // 4
        return f"#x{val:0{hex_digits}x}"
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(2**k, index_bits)  # 2^k in hex
    
    # Use 2^k notation for comments on large values
    if k <= 16:
        overflow_str = str(2**k)
        max_steps_str = str(2**k - 1)
        states_str = str(2**k)
    else:
        overflow_str = f"2^{k}"
        max_steps_str = f"2^{k}-1"
        states_str = f"2^{k}"
    
    return f"""; Zero-extend version of cex1: single variable x, property uses zero_extend
; Equivalent to bv{k}_cex1.smt2 but with pure BV property (no bv2int)
;
; Original property: (not (< (+ 1 (bv2int x)) {overflow_str}))
; With zero_extend: NOT(bvult(bvadd(zext(x), 1), {overflow_str}))
;
; Trace: x=0,1,2,...,{max_steps_str} ({states_str} states)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (= x_next (bvadd x {x_one})))
        (inv x_next))
  )
)

; Property: zero_extend(x) + 1 < {overflow_str} (violated when x = {max_steps_str})
(assert 
  (forall ((x (_ BitVec {k})))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend {k}) x) {ext_one}) {ext_max})))
        false)
  )
)

(check-sat)
"""

def generate_ccex(k):
    """Generate CCEX file for k-bit zero-extend benchmark."""
    index_bits = 2 * k
    
    # Format hex values
    def hex_val(val, bits):
        hex_digits = (bits + 3) // 4
        return f"#x{val:0{hex_digits}x}"
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(2**k - 1, index_bits)  # 2^k - 1 in hex
    
    # For comments, use 2^k notation for large values
    if k <= 16:
        bounds_str = f"0 to {2**k - 1} ({2**k} states)"
    else:
        bounds_str = f"0 to 2^{k}-1 (2^{k} states)"
    
    return f"""; Compact CEX for {k}-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower {k} bits of {index_bits}-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(declare-const trace (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule {idx_zero} i) (bvule i {idx_max})) 
        (= (select trace i) (x_at_i i))
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
