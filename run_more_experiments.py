
import os

def to_hex16(val):
    val = int(val)
    if val < 0:
        val = (val + 65536) % 65536
    return f"#x{val:04x}"

def generate_sygus_file(filename, state_vars, trace_len, constants, logic_logic="BV"):
    with open(filename, 'w') as f:
        f.write(f"(set-logic {logic_logic})\n")
        
        for name in state_vars.keys():
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            # Bag of Constants
            seen_consts = set()
            for c in constants:
                h = to_hex16(c)
                if h not in seen_consts:
                    f.write(f"    {h}\n")
                    seen_consts.add(h)
            
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            f.write("    (ite MyBool Start Start)\n")
            f.write("    (bvurem Start Start)\n")  # Added for s_split_14 (mod)
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
            f.write("     (bvult Start Start)\n")
            f.write("     (bvuge Start Start)\n")
            f.write("     (= Start Start)\n")
            f.write("   )))\n")
            f.write(")\n\n")
            
        for i in range(trace_len):
             hex_i = to_hex16(i)
             for name, vals in state_vars.items():
                 # Handle list index out of range if trace shorter
                 if i < len(vals):
                    hex_val = to_hex16(vals[i])
                    f.write(f"(constraint (= ({name} {hex_i}) {hex_val}))\n")
        
        f.write("\n(check-synth)\n")
    print(f"Generated {filename}")

def run_s_split_14():
    # s_split_14.smt2
    # x0=-100, z0=-100
    # x1 = (x0+1) % 5
    # z1 = (z0+1) if z0 < 4 else (z0 % 4)
    # Constants: -100, 1, 5, 4, 0
    
    trace_x = []
    trace_z = []
    
    x, z = -100, -100
    # Run for 250 steps
    for _ in range(250):
        trace_x.append(x)
        trace_z.append(z)
        
        # SMT 'mod' usually Euclidean. Python % is also often fine but let's be careful with negatives.
        # solver: (= x1 (mod (+ x0 1) 5))
        # z: if z<4 then z+1 else z%4
        
        # x update
        # In SMTIB, mod is always positive.
        next_x = (x + 1)
        # Emulate SMT mod for negative? (-99 mod 5) = 1. Python: -99 % 5 = 1. Matches.
        x = next_x % 5
        
        # z update
        if z < 4:
            z = z + 1
        else:
            z = z % 4
            
    generate_sygus_file(
        "s_split_14_user.sygus",
        {"fx": trace_x, "fz": trace_z},
        250,
        [-100, 1, 5, 4, 0]
    )

def run_s_split_48():
    # s_split_48.smt2
    # x0=0, y0=0
    # x++
    # phases: <4000 (+4), <5000 (+1), <6000 (-1), else (-4)
    # Constants: 0, 1, 4, 4000, 5000, 6000, 10000
    
    trace_x = []
    trace_y = []
    
    x, y = 0, 0
    # Run to 10005
    for _ in range(10005):
        trace_x.append(x)
        trace_y.append(y)
        
        next_x = x + 1
        
        if x < 5000:
            if x >= 4000:
                y = y + 4
            else:
                y = y + 1
        else:
            if x >= 6000:
                y = y - 1 # wait, check smt.
                # (ite (>= x0 6000) (- y0 1) (- y0 4))
            else:
                y = y - 4
        
        x = next_x
        
    generate_sygus_file(
        "s_split_48_user.sygus",
        {"fx": trace_x, "fy": trace_y},
        10005,
        [0, 1, 4, 4000, 5000, 6000, 10000]
    )

if __name__ == "__main__":
    run_s_split_14()
    run_s_split_48()
