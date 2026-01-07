#!/usr/bin/env python3
"""
Generate complex benchmarks for Inductive CCEX validation.
Categories:
1. Polynomial: x(i) = i^2
2. Bitwise: Gray code pattern x(i) = i ^ (i >> 1)
3. Saturation: x(i) = min(i, limit)
4. Alternating: x(i) = i if even, -i if odd
"""

import os
import sys

OUTPUT_DIR = "complex"

def hex_val(val, bits):
    """Format a value as a hex literal with appropriate width."""
    hex_digits = (bits + 3) // 4
    return f"#x{val:0{hex_digits}x}"

def ensure_dir(directory):
    if not os.path.exists(directory):
        os.makedirs(directory)

# =============================================================================
# 1. POLYNOMIAL: x(i) = i^2
# =============================================================================
def generate_polynomial_chc(k):
    """
    x tracks i^2.
    Relation: (i+1)^2 = i^2 + 2i + 1
    State: (c, x) where c is counter i, x is c^2
    Trans: c' = c + 1, x' = x + 2c + 1
    """
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_two = hex_val(2, k)
    
    # Calculate max steps before overflow of i^2
    # i^2 < 2^k  => i < 2^(k/2)
    max_steps = int(2**(k/2)) - 1
    max_steps_hex = hex_val(max_steps, k)
    
    return f"""; Polynomial growth: x = i^2
; State: (c, x) where c is counter, x is c^2
; Trans: c' = c + 1, x' = x + 2c + 1
; Bound: c < {max_steps} (approx 2^(k/2))

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Init: c=0, x=0
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (= c {x_zero}) (= x {x_zero})) (inv c x))
  )
)

; Trans: c' = c+1, x' = x + 2c + 1
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})) 
           (c_next (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv c x)
             (= c_next (bvadd c {x_one}))
             (= x_next (bvadd x (bvadd (bvmul {x_two} c) {x_one}))))
        (inv c_next x_next))
  )
)

; Property: x reaches max_steps^2
; We check if we can reach the state where x = max_steps^2
; The negation is: if x = max_steps^2 then false
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (inv c x) 
             (= x #x{max_steps**2:0{k//4}x}))
        false)
  )
)

(check-sat)
"""

def generate_polynomial_ccex(k):
    """CCEX: x(i) = i^2, c(i) = i"""
    # i^2 < 2^k  => i < 2^(k/2)
    max_steps = int(2**(k/2)) - 1
    
    # Index bits needs to be enough to hold max_steps
    # For k=4, max=3, index=4 is fine.
    # For k=32, max=65535, index=32 is fine.
    index_bits = k 
    
    return f"""; CCEX for Polynomial: x(i) = i^2
; c(i) = i
; x(i) = i*i
; Trace bounds: 0 to {max_steps}

(define-fun c_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  i
)

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (bvmul i i)
)

(declare-const trace_c (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule #x{0:0{k//4}x} i) (bvule i #x{max_steps:0{k//4}x})) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
"""

# =============================================================================
# 2. BITWISE: Gray Code x(i) = i ^ (i >> 1)
# =============================================================================
def generate_bitwise_chc(k):
    """
    x tracks Gray code of i.
    State: (c, x)
    Trans: c' = c + 1, x' = c' ^ (c' >> 1)
    """
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    max_steps = 2**k - 1
    max_steps_hex = hex_val(max_steps, k)
    
    # Expected x at max_steps: max_steps ^ (max_steps >> 1)
    # max_steps is all 1s. max_steps >> 1 is 011...1.
    # XOR gives 100...0 (top bit set).
    expected_x = max_steps ^ (max_steps >> 1)
    expected_x_hex = hex_val(expected_x, k)
    
    return f"""; Bitwise pattern: Gray Code x = i ^ (i >> 1)
; State: (c, x)
; Trans: c' = c + 1, x' = c' ^ (c' >> 1)

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Init: c=0, x=0
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (= c {x_zero}) (= x {x_zero})) (inv c x))
  )
)

; Trans
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})) 
           (c_next (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv c x)
             (bvult c {max_steps_hex})
             (= c_next (bvadd c {x_one}))
             (= x_next (bvxor c_next (bvlshr c_next {x_one}))))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (inv c x) 
             (= x {expected_x_hex}))
        false)
  )
)

(check-sat)
"""

def generate_bitwise_ccex(k):
    index_bits = k
    max_steps = 2**k - 1
    
    return f"""; CCEX for Gray Code
; c(i) = i
; x(i) = i ^ (i >> 1)

(define-fun c_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  i
)

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (bvxor i (bvlshr i #x{1:0{k//4}x}))
)

(declare-const trace_c (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule #x{0:0{k//4}x} i) (bvule i #x{max_steps:0{k//4}x})) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
"""

# =============================================================================
# 3. SATURATION: x(i) = min(i, limit)
# =============================================================================
def generate_saturation_chc(k):
    """
    x saturates at limit.
    State: (c, x)
    Trans: c' = c + 1, x' = if x < limit then x + 1 else x
    """
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    
    limit = 2**(k-1) # Saturate at half range
    limit_hex = hex_val(limit, k)
    
    max_steps = 2**k - 1
    max_steps_hex = hex_val(max_steps, k)
    
    return f"""; Saturation: x = min(i, {limit})
; State: (c, x)
; Trans: c' = c + 1, x' = if x < {limit} then x + 1 else x

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Init
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (= c {x_zero}) (= x {x_zero})) (inv c x))
  )
)

; Trans
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})) 
           (c_next (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv c x)
             (bvult c {max_steps_hex})
             (= c_next (bvadd c {x_one}))
             (= x_next (ite (bvult x {limit_hex}) (bvadd x {x_one}) x)))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (inv c x) 
             (= x {limit_hex}))
        false)
  )
)

(check-sat)
"""

def generate_saturation_ccex(k):
    index_bits = k
    max_steps = 2**k - 1
    limit = 2**(k-1)
    limit_hex = hex_val(limit, k)
    
    return f"""; CCEX for Saturation
; c(i) = i
; x(i) = ite(i < {limit}, i, {limit})

(define-fun c_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  i
)

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (ite (bvult i {limit_hex}) i {limit_hex})
)

(declare-const trace_c (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule #x{0:0{k//4}x} i) (bvule i #x{max_steps:0{k//4}x})) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
"""

# =============================================================================
# 4. ALTERNATING: x(i) = i if even, -i if odd
# =============================================================================
def generate_alternating_chc(k):
    """
    x alternates sign based on parity of i.
    State: (c, x)
    Trans: c' = c + 1, x' = if (c' & 1 == 0) then c' else -c'
    """
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    max_steps = 2**k - 1
    max_steps_hex = hex_val(max_steps, k)
    
    # Expected x at max_steps:
    # max_steps is odd (2^k - 1).
    # So x = -max_steps = -(2^k - 1) = 1 (mod 2^k)
    expected_x = 1
    expected_x_hex = hex_val(expected_x, k)
    
    return f"""; Alternating: x = i if even, -i if odd
; State: (c, x)
; Trans: c' = c + 1, x' = if (c' % 2 == 0) then c' else -c'

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Init
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (= c {x_zero}) (= x {x_zero})) (inv c x))
  )
)

; Trans
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})) 
           (c_next (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv c x)
             (bvult c {max_steps_hex})
             (= c_next (bvadd c {x_one}))
             (= x_next (ite (= (bvand c_next {x_one}) {x_zero}) 
                            c_next 
                            (bvneg c_next))))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec {k})) (x (_ BitVec {k})))
    (=> (and (inv c x) 
             (= x {expected_x_hex}))
        false)
  )
)

(check-sat)
"""

def generate_alternating_ccex(k):
    index_bits = k
    max_steps = 2**k - 1
    x_one = hex_val(1, k)
    x_zero = hex_val(0, k)
    
    return f"""; CCEX for Alternating
; c(i) = i
; x(i) = ite(i & 1 == 0, i, -i)

(define-fun c_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  i
)

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (ite (= (bvand i {x_one}) {x_zero}) i (bvneg i))
)

(declare-const trace_c (Array (_ BitVec {index_bits}) (_ BitVec {k})))
(declare-const trace_x (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule #x{0:0{k//4}x} i) (bvule i #x{max_steps:0{k//4}x})) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
"""

def main():
    ensure_dir(os.path.join(OUTPUT_DIR, "polynomial"))
    ensure_dir(os.path.join(OUTPUT_DIR, "bitwise"))
    ensure_dir(os.path.join(OUTPUT_DIR, "saturation"))
    ensure_dir(os.path.join(OUTPUT_DIR, "alternating"))
    
    # Bitwidths to generate
    # Note: Polynomial grows fast, so for k=4 max_steps=3. For k=8 max_steps=15.
    bitwidths = [8, 16, 32] 
    
    for k in bitwidths:
        print(f"Generating complex benchmarks for k={k}...")
        
        # 1. Polynomial
        with open(os.path.join(OUTPUT_DIR, "polynomial", f"bv{k}_poly.smt2"), "w") as f:
            f.write(generate_polynomial_chc(k))
        with open(os.path.join(OUTPUT_DIR, "polynomial", f"bv{k}_poly_ccex.smt2"), "w") as f:
            f.write(generate_polynomial_ccex(k))
            
        # 2. Bitwise
        with open(os.path.join(OUTPUT_DIR, "bitwise", f"bv{k}_gray.smt2"), "w") as f:
            f.write(generate_bitwise_chc(k))
        with open(os.path.join(OUTPUT_DIR, "bitwise", f"bv{k}_gray_ccex.smt2"), "w") as f:
            f.write(generate_bitwise_ccex(k))
            
        # 3. Saturation
        with open(os.path.join(OUTPUT_DIR, "saturation", f"bv{k}_sat.smt2"), "w") as f:
            f.write(generate_saturation_chc(k))
        with open(os.path.join(OUTPUT_DIR, "saturation", f"bv{k}_sat_ccex.smt2"), "w") as f:
            f.write(generate_saturation_ccex(k))
            
        # 4. Alternating
        with open(os.path.join(OUTPUT_DIR, "alternating", f"bv{k}_alt.smt2"), "w") as f:
            f.write(generate_alternating_chc(k))
        with open(os.path.join(OUTPUT_DIR, "alternating", f"bv{k}_alt_ccex.smt2"), "w") as f:
            f.write(generate_alternating_ccex(k))

if __name__ == "__main__":
    # Change to the directory where this script is located to ensure relative paths work
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    main()
