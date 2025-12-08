#!/usr/bin/env python3
"""
Generate SAFE versions of zext benchmarks.
These include a loop guard in the transition relation that prevents the NEXT state
from violating the property. The property should be SATISFIED (no counterexample exists).

Key insight: The guard must check that the NEXT state satisfies the property,
not the current state. So for property "zext(x)+1 < 2^k", the guard for 
transition "x' = x + 1" must be "zext(x)+2 < 2^k" (i.e., zext(x')+1 < 2^k).
"""

import os

def hex_val(val, bits):
    """Format a value as a hex literal with appropriate width."""
    hex_digits = (bits + 3) // 4
    return f"#x{val:0{hex_digits}x}"

# =============================================================================
# CEX1 SAFE: Single variable, increment by 1, with guard
# =============================================================================
def generate_cex1_safe_chc(k):
    """Single variable x incrementing by 1, with overflow guard on NEXT state."""
    index_bits = 2 * k
    max_val = 2**k - 1
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_two = hex_val(2, index_bits)  # For checking next state
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        max_val_str = str(max_val)
    else:
        overflow_str = f"2^{k}"
        max_val_str = f"2^{k}-1"
    
    return f"""; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < {overflow_str} (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < {overflow_str}
; Guard: zext(x)+2 < {overflow_str} (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= {max_val_str}-1

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < {overflow_str}
; This ensures the NEXT state x' will satisfy zext(x')+1 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend {k}) x) {ext_two}) {ext_max})
             (= x_next (bvadd x {x_one})))
        (inv x_next))
  )
)

; Property: zext(x)+1 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend {k}) x) {ext_one}) {ext_max})))
        false)
  )
)

(check-sat)
"""

# =============================================================================
# CEX2 SAFE: Two variables, both increment by 1, with guard
# =============================================================================
def generate_cex2_safe_chc(k):
    """Two variables x, y both incrementing by 1, with overflow guard on NEXT state."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_two = hex_val(2, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; SAFE zero-extend version of cex2: two variables x, y both increment by 1
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero})) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 1, ONLY when both next states satisfy property
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) 
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend {k}) x) {ext_two}) {ext_max})
             (bvult (bvadd ((_ zero_extend {k}) y) {ext_two}) {ext_max})
             (= x_next (bvadd x {x_one}))
             (= y_next (bvadd y {x_one})))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < {overflow_str} AND zext(y)+1 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend {k}) x) {ext_one}) {ext_max})
                       (bvult (bvadd ((_ zero_extend {k}) y) {ext_one}) {ext_max}))))
        false)
  )
)

(check-sat)
"""

# =============================================================================
# CEX3 SAFE: Three variables, all increment by 1, with guard
# =============================================================================
def generate_cex3_safe_chc(k):
    """Three variables x, y, z all incrementing by 1, with overflow guard on NEXT state."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_two = hex_val(2, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; SAFE zero-extend version of cex3: three variables x, y, z all increment by 1
; The transition only fires when ALL next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0, z = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero}) (= z {x_zero})) (inv x y z))
  )
)

; Transition: all increment by 1, ONLY when all next states satisfy property
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k}))
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})) (z_next (_ BitVec {k})))
    (=> (and (inv x y z)
             (bvult (bvadd ((_ zero_extend {k}) x) {ext_two}) {ext_max})
             (bvult (bvadd ((_ zero_extend {k}) y) {ext_two}) {ext_max})
             (bvult (bvadd ((_ zero_extend {k}) z) {ext_two}) {ext_max})
             (= x_next (bvadd x {x_one}))
             (= y_next (bvadd y {x_one}))
             (= z_next (bvadd z {x_one})))
        (inv x_next y_next z_next))
  )
)

; Property: all three must satisfy zext(v)+1 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k})))
    (=> (and (inv x y z) 
             (not (and (bvult (bvadd ((_ zero_extend {k}) x) {ext_one}) {ext_max})
                       (bvult (bvadd ((_ zero_extend {k}) y) {ext_one}) {ext_max})
                       (bvult (bvadd ((_ zero_extend {k}) z) {ext_one}) {ext_max}))))
        false)
  )
)

(check-sat)
"""

# =============================================================================
# CEX4 SAFE: Single variable incrementing by 2, with guard
# =============================================================================
def generate_cex4_safe_chc(k):
    """Single variable x incrementing by 2, with overflow guard on NEXT state."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_two = hex_val(2, k)
    ext_two = hex_val(2, index_bits)
    ext_four = hex_val(4, index_bits)  # Check x+2 will satisfy zext(x')+2 < 2^k
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; SAFE zero-extend version of cex4: single variable x incrementing by 2
; The transition only fires when zext(x)+4 < {overflow_str} (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 2, ONLY when zext(x)+4 < {overflow_str}
; This ensures x' = x+2 will satisfy zext(x')+2 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend {k}) x) {ext_four}) {ext_max})
             (= x_next (bvadd x {x_two})))
        (inv x_next))
  )
)

; Property: zext(x)+2 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend {k}) x) {ext_two}) {ext_max})))
        false)
  )
)

(check-sat)
"""

# =============================================================================
# CEX5 SAFE: Two variables, x += 1, y += 2, with guard
# =============================================================================
def generate_cex5_safe_chc(k):
    """Two variables: x += 1, y += 2, with overflow guard on NEXT state."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_two = hex_val(2, k)
    ext_one = hex_val(1, index_bits)
    ext_two = hex_val(2, index_bits)
    ext_four = hex_val(4, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; SAFE zero-extend version of cex5: x += 1, y += 2
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero})) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2, ONLY when both next states satisfy property
; x' satisfies prop when zext(x)+2 < {overflow_str}
; y' satisfies prop when zext(y)+4 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) 
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend {k}) x) {ext_two}) {ext_max})
             (bvult (bvadd ((_ zero_extend {k}) y) {ext_four}) {ext_max})
             (= x_next (bvadd x {x_one}))
             (= y_next (bvadd y {x_two})))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < {overflow_str} AND zext(y)+2 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend {k}) x) {ext_one}) {ext_max})
                       (bvult (bvadd ((_ zero_extend {k}) y) {ext_two}) {ext_max}))))
        false)
  )
)

(check-sat)
"""

# =============================================================================
# CEX6 SAFE: Single variable starting at 5, incrementing by 1, with guard
# =============================================================================
def generate_cex6_safe_chc(k):
    """Single variable x starting at 5, incrementing by 1, with overflow guard on NEXT state."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_five = hex_val(5, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_two = hex_val(2, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; SAFE zero-extend version of cex6: x starts at 5, increments by 1
; The transition only fires when zext(x)+2 < {overflow_str} (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 5
(assert 
  (inv {x_five})
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend {k}) x) {ext_two}) {ext_max})
             (= x_next (bvadd x {x_one})))
        (inv x_next))
  )
)

; Property: zext(x)+1 < {overflow_str}
(assert 
  (forall ((x (_ BitVec {k})))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend {k}) x) {ext_one}) {ext_max})))
        false)
  )
)

(check-sat)
"""

# =============================================================================
# Main: Generate all safe benchmarks
# =============================================================================
def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Bit widths to generate
    bit_widths = [4, 8, 16, 32, 64, 128, 256, 512, 1024]
    
    # Define benchmark generators (CHC only - no CCEX for safe versions)
    benchmarks = {
        'cex1_safe': generate_cex1_safe_chc,
        'cex2_safe': generate_cex2_safe_chc,
        'cex3_safe': generate_cex3_safe_chc,
        'cex4_safe': generate_cex4_safe_chc,
        'cex5_safe': generate_cex5_safe_chc,
        'cex6_safe': generate_cex6_safe_chc,
    }
    
    for bench_name, chc_gen in benchmarks.items():
        # Create directory
        bench_dir = os.path.join(script_dir, bench_name)
        os.makedirs(bench_dir, exist_ok=True)
        
        print(f"\n=== Generating {bench_name} ===")
        
        for k in bit_widths:
            # Generate CHC file
            chc_filename = f"bvzext{k}_{bench_name.replace('_safe', '')}_safe.smt2"
            chc_path = os.path.join(bench_dir, chc_filename)
            with open(chc_path, 'w') as f:
                f.write(chc_gen(k))
            print(f"  Generated {chc_filename}")

if __name__ == "__main__":
    main()
