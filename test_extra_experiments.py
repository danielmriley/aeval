
import os
from run_more_experiments import generate_sygus_file, to_hex16

# Shared grammar function with rich features
def generate_rich_sygus_file(filename, state_vars, constants, sparse_indices=None):
    with open(filename, 'w') as f:
        f.write(f"(set-logic BV)\n")
        
        for name in state_vars.keys():
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            seen = set()
            for c in constants:
                h = to_hex16(c)
                if h not in seen:
                    f.write(f"    {h}\n")
                    seen.add(h)
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            # f.write("    (bvmul Start Start)\n") # Opting out bvmul for s_split_42 to reduce search space, unless needed. 
            # s_split_42 is additive. 
            # s_split_11 has mod 2. 
            # Let's include bvshl (<<1 is *2) which is cheap.
            f.write("    (bvshl Start Start)\n")
            f.write("    (bvurem Start Start)\n") 
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
            f.write("     (bvult Start Start)\n")
            f.write("     (bvuge Start Start)\n")
            f.write("     (bvule Start Start)\n")
            f.write("     (bvugt Start Start)\n")
            f.write("     (= Start Start)\n")
            f.write("     (not (= Start Start))\n")
            f.write("   )))\n")
            f.write(")\n\n")
            
        # Constraints
        # Assuming state_vars[name] is a list corresponding to trace.
        # If sparse_indices is provided, only write those.
        # Otherwise write all 0..len
        
        trace_len = len(list(state_vars.values())[0])
        indices = sparse_indices if sparse_indices is not None else range(trace_len)
        
        for i in indices:
            if i >= trace_len: continue 
            hi = to_hex16(i)
            for name, vals in state_vars.items():
                hex_val = to_hex16(vals[i])
                f.write(f"(constraint (= ({name} {hi}) {hex_val}))\n")
        
        f.write("\n(check-synth)\n")
    print(f"Generated {filename}")

def run_s_split_11():
    # s_split_11.smt2
    # x0 random < 0. Let's pick -100.
    # z0 = 0 (can be 0 or 1). Pick 0.
    # y0 > x0. x=-100 -> y0=-90? Or y0=0. Let's pick y0=0.
    
    x, y, z = -100, 0, 0
    trace_x, trace_y = [], []
    
    limit = 55100 # > 54932
    
    for _ in range(limit):
        trace_x.append(x)
        trace_y.append(y)
        
        x_prev = x
        y_prev = y
        z_prev = z
        
        # Updates
        next_x = x_prev + 1
        
        # y1 = (ite (= (mod x0 2) z0) (+ y0 2) y0)
        # mod in python % is distinct for negatives.
        # x=-100%2 = 0. x=-99%2 = 1.
        # matches z0=0.
        cond = (x_prev % 2) == z_prev
        if cond:
            next_y = y_prev + 2
        else:
            next_y = y_prev
            
        x, y = next_x, next_y
        
    # sample every 100 but also some odd numbers to avoid aliasing
    indices = [i for i in range(0, limit, 100)]
    indices.extend([i+1 for i in range(0, 1000, 100)]) # Add 1, 101, 201...
    indices = sorted(list(set(indices)))
    # Add boundary 54932 (approx)
    indices.append(54932)
    indices.append(limit-1)
    
    generate_rich_sygus_file(
        "s_split_11_user.sygus",
        {"fx": trace_x, "fy": trace_y},
        [0, 1, 2, 54932, -100], # constants
        indices
    )

def run_s_split_42():
    # s_split_42.smt2
    # x=0, y=0, z=0
    x, y, z = 0, 0, 0
    trace_x, trace_y, trace_z = [], [], []
    
    limit = 17700 # > 17650
    
    for _ in range(limit):
        trace_x.append(x)
        trace_y.append(y)
        trace_z.append(z)
        
        x_prev, y_prev, z_prev = x, y, z
        
        next_x = x_prev + 1
        
        # y1 = (ite (>= x0 1765) (+ y0 2) (+ y0 1))
        if x_prev >= 1765:
            next_y = y_prev + 2
        else:
            next_y = y_prev + 1
            
        # z1 = (ite (>= y0 5765) (+ z0 3) (+ z0 2))
        if y_prev >= 5765:
            next_z = z_prev + 3
        else:
            next_z = z_prev + 2
            
        x, y, z = next_x, next_y, next_z
        
    # sample every 50
    indices = []
    for i in range(0, limit, 50):
        indices.append(i)
    
    boundaries = [1765, 3765, 17650] # 3765 is inferred phase 2
    for b in boundaries:
        for offset in range(-5, 6):
            if 0 <= b+offset < limit:
                indices.append(b+offset)
    
    indices = sorted(list(set(indices)))
    
    generate_rich_sygus_file(
        "s_split_42_user.sygus",
        {"fx": trace_x, "fy": trace_y, "fz": trace_z},
        [0, 1, 2, 3, 1765, 5765, 17650, 27650],
        indices
    )

if __name__ == "__main__":
    run_s_split_11()
    run_s_split_42()
