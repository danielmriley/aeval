#!/usr/bin/env python3
"""
Generate special benchmarks: Invalid and Partial CCEXs.
"""

import os
import sys

OUTPUT_DIR_INVALID = "invalid"
OUTPUT_DIR_PARTIAL = "partial"

def hex_val(val, bits):
    hex_digits = (bits + 3) // 4
    return f"#x{val:0{hex_digits}x}"

def ensure_dir(directory):
    if not os.path.exists(directory):
        os.makedirs(directory)

# =============================================================================
# 1. INVALID CCEX: Off-by-one error
# =============================================================================
def generate_invalid_chc(k):
    """Standard linear counter x' = x + 1."""
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    max_steps = 2**k - 1
    max_steps_hex = hex_val(max_steps, k)
    
    return f"""; Linear counter x' = x + 1
(set-logic HORN)
(declare-fun inv ((_ BitVec {k})) Bool)
(assert (forall ((x (_ BitVec {k}))) (=> (= x {x_zero}) (inv x))))
(assert (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x) (bvult x {max_steps_hex}) (= x_next (bvadd x {x_one}))) (inv x_next))))
(assert (forall ((x (_ BitVec {k}))) (=> (and (inv x) (= x {max_steps_hex})) false)))
(check-sat)
"""

def generate_invalid_ccex(k):
    """Invalid CCEX: x(i) = i + 1 (starts at 1 instead of 0)."""
    index_bits = k
    max_steps = 2**k - 1
    
    return f"""; INVALID CCEX: x(i) = i + 1 (Init violation)
(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (bvadd i #x{1:0{k//4}x})
)
(declare-const trace (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(assert (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule #x{0:0{k//4}x} i) (bvule i #x{max_steps:0{k//4}x})) 
        (= (select trace i) (x_at_i i)))))
(check-sat)
"""

# =============================================================================
# 2. PARTIAL CCEX: Cone of Influence
# =============================================================================
def generate_partial_chc(k):
    """
    System with 3 variables: x, y, z.
    x' = x + 1
    y' = y + 2
    z' = z + 3
    Property only checks x.
    """
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_two = hex_val(2, k)
    x_three = hex_val(3, k)
    max_steps = 2**k - 1
    max_steps_hex = hex_val(max_steps, k)
    
    return f"""; Partial system: x, y, z independent counters
; Property only depends on x
(set-logic HORN)
(declare-fun inv ((_ BitVec {k}) (_ BitVec {k}) (_ BitVec {k})) Bool)
(assert (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero}) (= z {x_zero})) (inv x y z))))
(assert (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k}))
                 (xn (_ BitVec {k})) (yn (_ BitVec {k})) (zn (_ BitVec {k})))
    (=> (and (inv x y z) (bvult x {max_steps_hex})
             (= xn (bvadd x {x_one}))
             (= yn (bvadd y {x_two}))
             (= zn (bvadd z {x_three})))
        (inv xn yn zn))))
(assert (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k})))
    (=> (and (inv x y z) (= x {max_steps_hex})) false)))
(check-sat)
"""

def generate_partial_ccex(k):
    """Partial CCEX: Only defines x(i). y and z are missing."""
    index_bits = k
    max_steps = 2**k - 1
    
    return f"""; PARTIAL CCEX: Only defines x(i)
; y and z are missing, but not needed for property violation
(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  i
)
(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))
; trace_y and trace_z are intentionally missing
(assert (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule #x{0:0{k//4}x} i) (bvule i #x{max_steps:0{k//4}x})) 
        (= (select trace_x i) (x_at_i i)))))
(check-sat)
"""

def main():
    ensure_dir(OUTPUT_DIR_INVALID)
    ensure_dir(OUTPUT_DIR_PARTIAL)
    
    bitwidths = [8, 16]
    
    for k in bitwidths:
        print(f"Generating special benchmarks for k={k}...")
        
        # 1. Invalid
        with open(os.path.join(OUTPUT_DIR_INVALID, f"bv{k}_invalid.smt2"), "w") as f:
            f.write(generate_invalid_chc(k))
        with open(os.path.join(OUTPUT_DIR_INVALID, f"bv{k}_invalid_ccex.smt2"), "w") as f:
            f.write(generate_invalid_ccex(k))
            
        # 2. Partial
        with open(os.path.join(OUTPUT_DIR_PARTIAL, f"bv{k}_partial.smt2"), "w") as f:
            f.write(generate_partial_chc(k))
        with open(os.path.join(OUTPUT_DIR_PARTIAL, f"bv{k}_partial_ccex.smt2"), "w") as f:
            f.write(generate_partial_ccex(k))

if __name__ == "__main__":
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
