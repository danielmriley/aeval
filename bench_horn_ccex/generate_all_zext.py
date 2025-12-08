#!/usr/bin/env python3
"""
Generate zero-extend versions of all cex benchmarks.
These use pure BV with zero_extend instead of bv2int/int2bv.
"""

import os

def hex_val(val, bits):
    """Format a value as a hex literal with appropriate width."""
    hex_digits = (bits + 3) // 4
    return f"#x{val:0{hex_digits}x}"

def bin_val(val, bits):
    """Format a value as a binary literal."""
    return f"#b{val:0{bits}b}"

# =============================================================================
# CEX2: Two variables, both increment by 1
# =============================================================================
def generate_cex2_chc(k):
    """Two variables x, y both incrementing by 1."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        max_steps_str = str(max_steps)
    else:
        overflow_str = f"2^{k}"
        max_steps_str = f"2^{k}-1"
    
    return f"""; Zero-extend version of cex2: two variables x, y both increment by 1
; Property: zext(x)+1 < {overflow_str} AND zext(y)+1 < {overflow_str}
; Trace: 0 to {max_steps_str}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero})) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 1
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) 
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})))
    (=> (and (inv x y)
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

def generate_cex2_ccex(k):
    """CCEX for cex2: both x and y are extract(i)."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    
    if k <= 16:
        bounds_str = f"0 to {max_steps}"
    else:
        bounds_str = f"0 to 2^{k}-1"
    
    return f"""; Compact CEX for {k}-bit cex2_zext: two variables, both increment by 1
; x_at_i(i) = extract(i), y_at_i(i) = extract(i)
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun y_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_y (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule {idx_zero} i) (bvule i {idx_max})) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
"""

# =============================================================================
# CEX3: Three variables, all increment by 1
# =============================================================================
def generate_cex3_chc(k):
    """Three variables x, y, z all incrementing by 1."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        max_steps_str = str(max_steps)
    else:
        overflow_str = f"2^{k}"
        max_steps_str = f"2^{k}-1"
    
    return f"""; Zero-extend version of cex3: three variables x, y, z all increment by 1
; Property: zext(x)+1 < {overflow_str} AND zext(y)+1 < {overflow_str} AND zext(z)+1 < {overflow_str}
; Trace: 0 to {max_steps_str}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0, z = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero}) (= z {x_zero})) (inv x y z))
  )
)

; Transition: x' = x + 1, y' = y + 1, z' = z + 1
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) (z (_ BitVec {k}))
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})) (z_next (_ BitVec {k})))
    (=> (and (inv x y z)
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

def generate_cex3_ccex(k):
    """CCEX for cex3: x, y, z are all extract(i)."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    
    if k <= 16:
        bounds_str = f"0 to {max_steps}"
    else:
        bounds_str = f"0 to 2^{k}-1"
    
    return f"""; Compact CEX for {k}-bit cex3_zext: three variables, all increment by 1
; x_at_i(i) = y_at_i(i) = z_at_i(i) = extract(i)
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun y_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun z_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_y (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_z (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule {idx_zero} i) (bvule i {idx_max})) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i))
             (= (select trace_z i) (z_at_i i)))
    )
  )
)

(check-sat)
"""

# =============================================================================
# CEX4: Single variable incrementing by 2
# =============================================================================
def generate_cex4_chc(k):
    """Single variable x incrementing by 2."""
    index_bits = 2 * k
    # x goes: 0, 2, 4, ..., 2^k-2, then overflows
    # Property fails when x + 2 >= 2^k, i.e., x >= 2^k - 2
    # This happens at step (2^k - 2) / 2 = 2^(k-1) - 1
    max_steps = 2**(k-1) - 1
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_two = hex_val(2, k)
    ext_two = hex_val(2, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        max_steps_str = str(max_steps)
    else:
        overflow_str = f"2^{k}"
        max_steps_str = f"2^{k-1}-1"
    
    return f"""; Zero-extend version of cex4: single variable x incrementing by 2
; x goes: 0, 2, 4, 6, ..., {overflow_str}-2, then violates property
; Property: zext(x)+2 < {overflow_str} (violated when x = {overflow_str}-2)
; Trace: 0 to {max_steps_str}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 2
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
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

def generate_cex4_ccex(k):
    """CCEX for cex4: x_at_i(i) = 2*i = extract(i << 1) or extract(i*2)."""
    index_bits = 2 * k
    max_steps = 2**(k-1) - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    
    if k <= 16:
        bounds_str = f"0 to {max_steps}"
    else:
        bounds_str = f"0 to 2^{k-1}-1"
    
    return f"""; Compact CEX for {k}-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower {k} bits of (i shifted left by 1)
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) (bvshl i #x{"0" * (index_bits // 4 - 1)}1))
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

# =============================================================================
# CEX5: Two variables, x += 1, y += 2
# =============================================================================
def generate_cex5_chc(k):
    """Two variables: x += 1, y += 2."""
    index_bits = 2 * k
    # y overflows first: y reaches 2^k-2 at step 2^(k-1)-1
    max_steps = 2**(k-1) - 1
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_two = hex_val(2, k)
    ext_one = hex_val(1, index_bits)
    ext_two = hex_val(2, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        max_steps_str = str(max_steps)
    else:
        overflow_str = f"2^{k}"
        max_steps_str = f"2^{k-1}-1"
    
    return f"""; Zero-extend version of cex5: x += 1, y += 2
; y overflows first at step {max_steps_str}
; Property: zext(x)+1 < {overflow_str} AND zext(y)+2 < {overflow_str}
; Trace: 0 to {max_steps_str}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero})) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) 
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})))
    (=> (and (inv x y)
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

def generate_cex5_ccex(k):
    """CCEX for cex5: x_at_i(i) = i, y_at_i(i) = 2*i."""
    index_bits = 2 * k
    max_steps = 2**(k-1) - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    
    if k <= 16:
        bounds_str = f"0 to {max_steps}"
    else:
        bounds_str = f"0 to 2^{k-1}-1"
    
    return f"""; Compact CEX for {k}-bit cex5_zext: x += 1, y += 2
; x_at_i(i) = extract(i), y_at_i(i) = extract(i << 1)
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun y_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) (bvshl i #x{"0" * (index_bits // 4 - 1)}1))
)

(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_y (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule {idx_zero} i) (bvule i {idx_max})) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
"""

# =============================================================================
# CEX6: Single variable starting at non-zero (5), incrementing by 1
# =============================================================================
def generate_cex6_chc(k):
    """Single variable x starting at 5, incrementing by 1."""
    index_bits = 2 * k
    # x goes: 5, 6, 7, ..., 2^k-1, then violates property
    # Property fails when x + 1 >= 2^k, i.e., x = 2^k - 1
    # Steps: 0 (x=5), 1 (x=6), ..., (2^k-1-5) (x=2^k-1)
    max_steps = 2**k - 1 - 5
    overflow_check = 2**k
    
    x_five = hex_val(5, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        max_steps_str = str(max_steps)
    else:
        overflow_str = f"2^{k}"
        max_steps_str = f"2^{k}-6"
    
    return f"""; Zero-extend version of cex6: x starts at 5, increments by 1
; x goes: 5, 6, 7, ..., {overflow_str}-1, then violates property
; Property: zext(x)+1 < {overflow_str}
; Trace: 0 to {max_steps_str}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 5
(assert 
  (inv {x_five})
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
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

def generate_cex6_ccex(k):
    """CCEX for cex6: x_at_i(i) = 5 + i = extract(i + 5)."""
    index_bits = 2 * k
    max_steps = 2**k - 1 - 5
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    idx_five = hex_val(5, index_bits)
    
    if k <= 16:
        bounds_str = f"0 to {max_steps}"
    else:
        bounds_str = f"0 to 2^{k}-6"
    
    return f"""; Compact CEX for {k}-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: {bounds_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) (bvadd i {idx_five}))
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

# =============================================================================
# Main: Generate all benchmarks
# =============================================================================
def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Bit widths to generate
    bit_widths = [4, 8, 16, 32, 64, 128, 256, 512, 1024]
    
    # Define benchmark generators
    benchmarks = {
        'cex2_zext': (generate_cex2_chc, generate_cex2_ccex),
        'cex3_zext': (generate_cex3_chc, generate_cex3_ccex),
        'cex4_zext': (generate_cex4_chc, generate_cex4_ccex),
        'cex5_zext': (generate_cex5_chc, generate_cex5_ccex),
        'cex6_zext': (generate_cex6_chc, generate_cex6_ccex),
    }
    
    for bench_name, (chc_gen, ccex_gen) in benchmarks.items():
        # Create directory
        bench_dir = os.path.join(script_dir, bench_name)
        os.makedirs(bench_dir, exist_ok=True)
        
        print(f"\n=== Generating {bench_name} ===")
        
        for k in bit_widths:
            # Generate CHC file
            chc_filename = f"bvzext{k}_{bench_name.replace('_zext', '')}.smt2"
            chc_path = os.path.join(bench_dir, chc_filename)
            with open(chc_path, 'w') as f:
                f.write(chc_gen(k))
            print(f"  Generated {chc_filename}")
            
            # Generate CCEX file
            ccex_filename = f"bvzext{k}_{bench_name.replace('_zext', '')}_ccex.smt2"
            ccex_path = os.path.join(bench_dir, ccex_filename)
            with open(ccex_path, 'w') as f:
                f.write(ccex_gen(k))
            print(f"  Generated {ccex_filename}")
        
        # Copy generator to benchmark directory
        gen_filename = f"generate_{bench_name}.py"
        gen_path = os.path.join(bench_dir, gen_filename)
        with open(gen_path, 'w') as f:
            f.write(f"# Generator script for {bench_name}\n")
            f.write(f"# Run generate_all_zext.py from parent directory to regenerate\n")

if __name__ == "__main__":
    main()
