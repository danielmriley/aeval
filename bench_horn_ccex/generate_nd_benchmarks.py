#!/usr/bin/env python3
"""
Generate nondeterministic and random-path benchmarks for CEX validation testing.

Benchmark types:
1. nd_cex1_zext: Nondeterministic choice (x++ OR y++), both reach max - zext version
2. nd_random: Random/arbitrary trace to error (explicit enumeration)
3. nd_mixed: Combination of continuous path + random jumps
4. nd_branch: Branching paths with different increments based on condition
5. nd_reset: Counter with nondeterministic reset
"""

import os
import random

def hex_val(val, bits):
    """Format a value as a hex literal with appropriate width."""
    hex_digits = (bits + 3) // 4
    return f"#x{val:0{hex_digits}x}"

# =============================================================================
# ND_CEX1_ZEXT: Nondeterministic x++ OR y++ (zext version of original)
# =============================================================================
def generate_nd_cex1_zext_chc(k):
    """Nondeterministic: either x increments OR y increments (not both)."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; Nondeterministic CEX: x++ OR y++ (not both) - zext version
; At each step, EITHER x increments by 1 OR y increments by 1
; Error when either variable overflows
; This creates exponentially many paths but a simple CCEX where x=y=i works

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero})) (inv x y))
  )
)

; Transition: EITHER x' = x + 1 (y unchanged) OR y' = y + 1 (x unchanged)
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) 
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})))
    (=> (and (inv x y)
             (or (and (= x_next (bvadd x {x_one})) (= y_next y))
                 (and (= x_next x) (= y_next (bvadd y {x_one})))))
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

def generate_nd_cex1_zext_ccex(k):
    """CCEX for nd_cex1: x always increments, y stays at 0."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    x_zero = hex_val(0, k)
    
    return f"""; CCEX for nd_cex1_zext: x increments, y stays at 0
; This represents the path where we always choose to increment x
; x goes 0,1,2,...,{max_steps} while y stays at 0
; Error occurs when x overflows (x = {max_steps}, zext(x)+1 >= 2^k)
; Trace bounds: 0 to {max_steps}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun y_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  {x_zero}
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
# ND_RANDOM: Random/explicit trace to error (no closed-form formula)
# =============================================================================
def generate_nd_random_chc(k):
    """System with arbitrary transitions - any value change allowed."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; Random-path CEX: x can take ANY value at each step
; This models a system with completely nondeterministic transitions
; The CCEX must enumerate explicit values for each step

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' can be ANY value (completely nondeterministic)
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (inv x)
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

def generate_nd_random_ccex(k, seed=42):
    """CCEX with explicit random values for each step."""
    index_bits = 2 * k
    max_val = 2**k - 1
    
    # Generate a random path that ends at max_val
    random.seed(seed)
    num_steps = min(16, 2**k)  # Keep trace short for readability
    
    # Generate random values, ensuring we end at max_val
    values = [0]  # Start at 0
    for i in range(1, num_steps - 1):
        values.append(random.randint(0, max_val - 1))
    values.append(max_val)  # End at max to violate property
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(num_steps - 1, index_bits)
    
    # Generate ITE chain for value function
    ite_chain = f"(ite (= i {hex_val(num_steps - 1, index_bits)}) {hex_val(values[-1], k)}\n"
    for i in range(num_steps - 2, 0, -1):
        ite_chain += f"    (ite (= i {hex_val(i, index_bits)}) {hex_val(values[i], k)}\n"
    ite_chain += f"    {hex_val(values[0], k)}" + ")" * (num_steps - 1)
    
    return f"""; CCEX for nd_random: explicit enumeration of random path
; This is NOT a closed-form function - it enumerates each step explicitly
; Values: {values}
; Trace bounds: 0 to {num_steps - 1}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  {ite_chain}
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
# ND_MIXED: Continuous path with random jumps
# =============================================================================
def generate_nd_mixed_chc(k):
    """System that mostly increments but can make random jumps."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; Mixed CEX: x usually increments by 1, but can jump to any value
; Models a system with a "normal" path plus nondeterministic resets/jumps

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 1 OR x' = anything (nondeterministic jump)
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (or (= x_next (bvadd x {x_one}))
                 true))  ; Can also jump to any value
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

def generate_nd_mixed_ccex(k):
    """CCEX for nd_mixed: standard linear path (the "simple" witness)."""
    # The simplest witness is just the linear path x = i
    index_bits = 2 * k
    max_steps = 2**k - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    
    return f"""; CCEX for nd_mixed: simple linear path x = i
; Even though the system allows jumps, the linear path is a valid witness
; Trace bounds: 0 to {max_steps}

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

# =============================================================================
# ND_BRANCH: Branching based on odd/even (x % 2 = 0 ? x+1 : x+2)
# =============================================================================
def generate_nd_branch_chc(k):
    """System with conditional branching: different increments based on parity.
    
    If x is even, increment by 1 (x' = x + 1).
    If x is odd, increment by 2 (x' = x + 2).
    
    This creates a sequence: 0, 1, 3, 5, 7, 9, ... which always reaches 2^k-1.
    Steps: 0→1 (+1), 1→3 (+2), 3→5 (+2), ... 
    Total steps to reach 2^k-1: 1 + (2^k-2)/2 = 2^(k-1)
    """
    index_bits = 2 * k
    overflow_check = 2**k
    max_val = 2**k - 1
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_two = hex_val(2, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; Branching CEX: (x mod 2 = 0) ? x+1 : x+2
; Even x: increment by 1
; Odd x: increment by 2
; Path: 0 → 1 → 3 → 5 → 7 → ... → {max_val}

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: if LSB is 0 (even) then x+1 else x+2
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (or (and (= ((_ extract 0 0) x) (_ bv0 1)) (= x_next (bvadd x {x_one})))
                 (and (= ((_ extract 0 0) x) (_ bv1 1)) (= x_next (bvadd x {x_two})))))
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

def generate_nd_branch_ccex(k):
    """CCEX for nd_branch: path following the parity rule.
    
    Path: 0 → 1 → 3 → 5 → 7 → ... → 2^k-1
    
    Step 0: x = 0 (even, so +1)
    Step 1: x = 1 (odd, so +2)
    Step 2: x = 3 (odd, so +2)
    ...
    Step n: x = 1 + 2*(n-1) = 2*n - 1 (for n >= 1)
    
    So: x(0) = 0, x(i) = 2*i - 1 for i >= 1
    
    To reach 2^k - 1: 2*n - 1 = 2^k - 1 => n = 2^(k-1)
    Total steps: 2^(k-1)
    """
    index_bits = 2 * k
    max_val = 2**k - 1
    total_steps = 2**(k-1)
    
    idx_zero = hex_val(0, index_bits)
    idx_one = hex_val(1, index_bits)
    idx_max = hex_val(total_steps, index_bits)
    
    if k <= 16:
        total_str = str(total_steps)
    else:
        total_str = f"2^{k-1}"
    
    return f"""; CCEX for nd_branch: parity-based path
; x(0) = 0, x(i) = 2*i - 1 for i >= 1
; Path: 0, 1, 3, 5, 7, ..., {max_val}
; Trace bounds: 0 to {total_str}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (ite (= i {idx_zero})
    (_ bv0 {k})
    (bvsub (bvshl ((_ extract {k-1} 0) i) (_ bv1 {k})) (_ bv1 {k}))
  )
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
# ND_RESET: Counter with nondeterministic reset to 0
# =============================================================================
def generate_nd_reset_chc(k):
    """Counter that can nondeterministically reset to 0."""
    index_bits = 2 * k
    overflow_check = 2**k
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; Reset CEX: x increments OR resets to 0
; This creates infinite loops that can be escaped by never resetting

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 1 OR x' = 0 (nondeterministic reset)
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (or (= x_next (bvadd x {x_one}))
                 (= x_next {x_zero})))
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

def generate_nd_reset_ccex(k):
    """CCEX for nd_reset: simple linear path (never reset)."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    
    return f"""; CCEX for nd_reset: linear path (always increment, never reset)
; Trace bounds: 0 to {max_steps}

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

# =============================================================================
# ND_TWOPHASE: Two variables with phase-dependent behavior
# =============================================================================
def generate_nd_twophase_chc(k):
    """Two variables: x always increments, y increments only when x >= threshold."""
    index_bits = 2 * k
    overflow_check = 2**k
    threshold = 2**(k-1)
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_thresh = hex_val(threshold, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
        thresh_str = str(threshold)
    else:
        overflow_str = f"2^{k}"
        thresh_str = f"2^{k-1}"
    
    return f"""; Two-phase CEX: x always increments, y increments only when x >= {thresh_str}
; Phase 1 (x < {thresh_str}): x++, y stays at 0
; Phase 2 (x >= {thresh_str}): x++, y++
; y reaches max after x does

(set-logic HORN)

(declare-fun inv ((_ BitVec {k}) (_ BitVec {k})) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})))
    (=> (and (= x {x_zero}) (= y {x_zero})) (inv x y))
  )
)

; Transition: x always increments, y increments only when x >= threshold
(assert 
  (forall ((x (_ BitVec {k})) (y (_ BitVec {k})) 
           (x_next (_ BitVec {k})) (y_next (_ BitVec {k})))
    (=> (and (inv x y)
             (= x_next (bvadd x {x_one}))
             (ite (bvuge x {x_thresh})
                  (= y_next (bvadd y {x_one}))
                  (= y_next y)))
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

def generate_nd_twophase_ccex(k):
    """CCEX for nd_twophase: x = i, y = max(0, i - threshold)."""
    index_bits = 2 * k
    max_steps = 2**k - 1
    threshold = 2**(k-1)
    
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(max_steps, index_bits)
    idx_thresh = hex_val(threshold, index_bits)
    x_zero = hex_val(0, k)
    
    if k <= 16:
        thresh_str = str(threshold)
    else:
        thresh_str = f"2^{k-1}"
    
    return f"""; CCEX for nd_twophase: x = i, y = max(0, i - {thresh_str})
; x follows linear path
; y is 0 until i >= {thresh_str}, then y = i - {thresh_str}
; Trace bounds: 0 to {max_steps}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(define-fun y_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  (ite (bvult i {idx_thresh})
    {x_zero}
    ((_ extract {k-1} 0) (bvsub i {idx_thresh}))
  )
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
# Main: Generate all benchmarks
# =============================================================================

# =============================================================================
# ND_SKIP: Constrained random path (x' = x+1 OR x' = x+3)
# =============================================================================
def generate_nd_skip_chc(k):
    """System with constrained nondeterminism: step by 1 or skip by 3.
    
    Transition: x' = x + 1  OR  x' = x + 3
    
    To reach exactly 2^k - 1, you need a specific sequence of +1 and +3 moves.
    For example, for k=4 (max=15): 0→1→4→5→8→9→12→13→14→15 (5 +1s and 4 +3s)
    """
    index_bits = 2 * k
    overflow_check = 2**k
    max_val = 2**k - 1
    
    x_zero = hex_val(0, k)
    x_one = hex_val(1, k)
    x_three = hex_val(3, k)
    ext_one = hex_val(1, index_bits)
    ext_max = hex_val(overflow_check, index_bits)
    
    if k <= 16:
        overflow_str = str(overflow_check)
    else:
        overflow_str = f"2^{k}"
    
    return f"""; Constrained nondeterministic: x' = x+1 OR x' = x+3
; Must reach exactly {max_val} to violate property
; Requires specific sequence of +1 and +3 choices

(set-logic HORN)

(declare-fun inv ((_ BitVec {k})) Bool)

; Initial state: x = 0
(assert 
  (inv {x_zero})
)

; Transition: x' = x + 1 OR x' = x + 3
(assert 
  (forall ((x (_ BitVec {k})) (x_next (_ BitVec {k})))
    (=> (and (inv x)
             (or (= x_next (bvadd x {x_one}))
                 (= x_next (bvadd x {x_three}))))
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

def compute_skip_path(max_val, max_steps=24):
    """Compute a path using +1 and +3 steps to reach exactly max_val.
    
    For small max_val: enumerate full path
    For large max_val: generate a short random-looking path that's valid
    
    Strategy: Generate a sequence of +1 and +3 steps that sums to max_val.
    We need: sum of steps = max_val, where each step is 1 or 3.
    
    For large values, we use mostly +3s with some +1s mixed in.
    """
    if max_val <= max_steps * 3:
        # Small enough to enumerate fully
        path = [0]
        current = 0
        random.seed(max_val)
        
        while current < max_val:
            remaining = max_val - current
            
            if remaining >= 3:
                if random.random() < 0.4:
                    current += 3
                else:
                    current += 1
            elif remaining >= 1:
                current += 1
            else:
                break
                
            path.append(current)
        
        return path
    else:
        # For large values, generate a fixed-length interesting path
        # We need steps that sum to max_val
        # Use a mix of +1 and +3 that sums correctly
        
        random.seed(max_val)
        num_steps = max_steps
        
        # We want: 1*a + 3*b = max_val, a + b = num_steps
        # So: a + 3*(num_steps - a) = max_val
        #     a + 3*num_steps - 3*a = max_val
        #     -2*a = max_val - 3*num_steps
        #     a = (3*num_steps - max_val) / 2
        
        # But this may not work for arbitrary max_val, so we adjust
        # Instead, compute: how many +3s and +1s to reach max_val in num_steps
        # 3*b + 1*a = max_val, a + b = num_steps
        # => 3*b + (num_steps - b) = max_val
        # => 2*b = max_val - num_steps
        # => b = (max_val - num_steps) / 2
        
        # This only works if (max_val - num_steps) is even and b <= num_steps
        # Otherwise we need to adjust num_steps
        
        # Find valid num_steps
        for n in range(max_steps, max_steps + 3):
            if (max_val - n) % 2 == 0:
                b = (max_val - n) // 2  # number of +3s
                a = n - b               # number of +1s
                if a >= 0 and b >= 0 and a + b == n:
                    num_steps = n
                    break
        else:
            # Fallback: just use linear path indicator
            return None
        
        # Generate a random arrangement of a +1s and b +3s
        steps = [1] * a + [3] * b
        random.shuffle(steps)
        
        # Build path
        path = [0]
        current = 0
        for s in steps:
            current += s
            path.append(current)
        
        return path

def generate_nd_skip_ccex(k):
    """CCEX for nd_skip: explicit path with +1 and +3 steps."""
    index_bits = 2 * k
    max_val = 2**k - 1
    
    # Compute the path
    path = compute_skip_path(max_val)
    
    # If path computation failed or path is too long, use linear path
    if path is None or len(path) > 64:
        # For very large paths, just use linear (all +1s) for simplicity
        # This is still valid since +1 is always allowed
        return f"""; CCEX for nd_skip: linear path (all +1 steps)
; For large bit widths, using simple x = i path
; Trace bounds: 0 to {max_val}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  ((_ extract {k-1} 0) i)
)

(declare-const trace (Array (_ BitVec {index_bits}) (_ BitVec {k})))

(assert 
  (forall ((i (_ BitVec {index_bits}))) 
    (=> (and (bvule {hex_val(0, index_bits)} i) (bvule i {hex_val(max_val, index_bits)})) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
"""
    
    num_steps = len(path)
    idx_zero = hex_val(0, index_bits)
    idx_max = hex_val(num_steps - 1, index_bits)
    
    # Generate ITE chain
    ite_chain = f"(ite (= i {hex_val(num_steps - 1, index_bits)}) {hex_val(path[-1], k)}\n"
    for j in range(num_steps - 2, 0, -1):
        ite_chain += f"    (ite (= i {hex_val(j, index_bits)}) {hex_val(path[j], k)}\n"
    ite_chain += f"    {hex_val(path[0], k)}" + ")" * (num_steps - 1)
    
    # Show the step sequence
    steps = []
    for j in range(1, len(path)):
        diff = path[j] - path[j-1]
        steps.append(f"+{diff}")
    step_str = ", ".join(steps[:20])
    if len(steps) > 20:
        step_str += f", ... ({len(steps)} steps total)"
    
    return f"""; CCEX for nd_skip: explicit path with +1 and +3 steps
; Path: {path[:10]}{'...' if len(path) > 10 else ''}
; Steps: {step_str}
; Total steps: {num_steps - 1}, final value: {max_val}
; Trace bounds: 0 to {num_steps - 1}

(define-fun x_at_i ((i (_ BitVec {index_bits}))) (_ BitVec {k})
  {ite_chain}
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
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Bit widths to generate
    bit_widths = [4, 8, 16, 32, 64]
    
    # Define benchmark generators
    benchmarks = {
        'nd_cex1_zext': (generate_nd_cex1_zext_chc, generate_nd_cex1_zext_ccex),
        'nd_random': (generate_nd_random_chc, generate_nd_random_ccex),
        'nd_mixed': (generate_nd_mixed_chc, generate_nd_mixed_ccex),
        'nd_branch': (generate_nd_branch_chc, generate_nd_branch_ccex),
        'nd_reset': (generate_nd_reset_chc, generate_nd_reset_ccex),
        'nd_twophase': (generate_nd_twophase_chc, generate_nd_twophase_ccex),
        'nd_skip': (generate_nd_skip_chc, generate_nd_skip_ccex),
    }
    
    for bench_name, (chc_gen, ccex_gen) in benchmarks.items():
        # Create directory
        bench_dir = os.path.join(script_dir, bench_name)
        os.makedirs(bench_dir, exist_ok=True)
        
        print(f"\n=== Generating {bench_name} ===")
        
        for k in bit_widths:
            # Generate CHC file
            chc_filename = f"bvzext{k}_{bench_name}.smt2"
            chc_path = os.path.join(bench_dir, chc_filename)
            with open(chc_path, 'w') as f:
                f.write(chc_gen(k))
            print(f"  Generated {chc_filename}")
            
            # Generate CCEX file
            ccex_filename = f"bvzext{k}_{bench_name}_ccex.smt2"
            ccex_path = os.path.join(bench_dir, ccex_filename)
            with open(ccex_path, 'w') as f:
                f.write(ccex_gen(k))
            print(f"  Generated {ccex_filename}")

if __name__ == "__main__":
    main()
