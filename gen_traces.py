
import os

def generate_sygus_file(filename, trace_len, state_vars_dict, transitions, init_vals):
    # This function generates a SyGuS file similar to s_split_experiment.sygus
    # But for an arbitrary trace.
    
    # Generic Grammar for phase guards
    # We allow the solver to synthesize boolean structure using comparisons with constants.
    # The constants should probably include values seen in the trace.
    
    # state_vars_dict: name -> list of values
    
    with open(filename, 'w') as f:
        f.write("(set-logic BV)\n")
        
        # Define functions for each state variable
        # Grammar: 
        # Start -> MyBool ? Start : Start | bvadd... | constants | n
        
        for name in state_vars_dict.keys():
            # (synth-fun name ((n (_ BitVec 16))) (_ BitVec 16) ...grammar...)
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            f.write("    #x0000\n")
            f.write("    #x0001\n")
            f.write("    #x0002\n")
            # Include some context specifics if needed, or generic:
            for val in [5000, 100, 10]: # Heuristic constants from generic templates
                 f.write(f"    (_ bv{val} 16)\n") 
                 
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            f.write("    (bvneg Start)\n")
            # f.write("    (bvmul Start Start)\n") # Mul is expensive?
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
            # Generic predicates
            # Allow comparisons of 'n' with ANY constant (this is what "generic phase guards" implies)
            # Actually standard SyGuS grammars for constants often use (Constant Int)
            # For BV, it's specific.
            # Let's add (bvult n Constant) where Constant is in the grammar?
            # Or just hardcode a few ranges?
            # "give it several choices in the MyBool function... to see if it can synthesize"
            
            f.write("     (bvuge n #x0000)\n") # Trivial
            # Add trace length as constant?
            f.write(f"     (bvuge n (_ bv{trace_len} 16))\n")
            f.write(f"     (bvult n (_ bv{trace_len//2} 16))\n")
            
            # The prompt says: "give it several choices... for general phase guards"
            # It implies maybe (bvult n C)
            f.write("     (bvult n #x0005)\n") 
            f.write("     (bvult n #x000A)\n") 
            f.write("     (bvult n #x0010)\n") # 16
            f.write("     (bvult n #x0064)\n") # 100
             
            f.write("     (bvult Start Start)\n")
            f.write("     (= Start Start)\n")
            f.write("   )))\n")
            f.write(")\n\n")

        # Constraints for every step
        for i in range(trace_len):
             hex_i = f"#x{i:04x}"
             for name, vals in state_vars_dict.items():
                 val = vals[i]
                 # Handle negative
                 if val < 0: val += 65536
                 hex_val = f"#x{val:04x}"
                 f.write(f"(constraint (= ({name} {hex_i}) {hex_val}))\n")
                 
        f.write("\n(check-synth)\n")
    
    print(f"Generated {filename} with trace length {trace_len}")

def simulate_05_and_21():
    # Simulate s_split_05
    # x0 > 0, y0 < 0, z0 = 1
    # Let's pick concrete: x=1, y=-20, z=1
    # Trace:
    # 0: x=1, y=-20, z=1. (Fail: y>=1 and z>1? No)
    # 1: x=2, y=-18. z = (y>=0 ? 2*z : z). -18<0 -> z=1.
    # ...
    # Step N: y becomes >= 0.
    # y = -20 + 2*N. y>=0 when 2N >= 20 -> N=10.
    # At N=10: y=0. z=1. (Previous step y=-2 < 0 so z stayed 1).
    # Step 11: updated using y=0 (old y).
    # Wait, transition: y1 = y0 + 2. z1 = (y0 >= 0 ...).
    # At step 10 (index): y=0.
    # x=11, y=2. z1 = (0 >= 0 ? 2 : 1) = 2.
    # So at step 11: z=2.
    # Fail cond: y >= x AND z > 1.
    # z > 1 is met.
    # y >= x? 
    # x = 1 + N. y = -20 + 2N.
    # -20 + 2N >= 1 + N  --> N >= 21.
    # So at step 21: x=22, y=-20+42=22. y >= x holds.
    # Fail reachable at step 21. 
    # Trace length ~22 steps. Perfect.
    
    # Generate trace 05
    trace_05_x = []
    trace_05_y = []
    trace_05_z = []
    x, y, z = 1, -20, 1
    for i in range(25): # Go a bit past 21
        trace_05_x.append(x)
        trace_05_y.append(y)
        trace_05_z.append(z)
        
        # Next
        old_y = y
        old_z = z
        x = x + 1
        y = y + 2
        if old_y >= 0:
            z = old_z * 2
        else:
            z = old_z
            
    generate_sygus_file("s_split_05_trace.sygus", 25, 
                        {"fx": trace_05_x, "fy": trace_05_y, "fz": trace_05_z}, 
                        None, None)

    # Simulate s_split_21
    # x0=0, y0=1, z0=0, w0=1
    # x += 1. y += 2. w = 1 - w (flips 0/1).
    # cond = ((x+y)%2 == w).
    # (0+1)%2 = 1 == 1. True. z += 1.
    # Step 1: x=1, y=3, w=0, z=1.
    # (1+3)%2 = 0 == 0. True. z += 1.
    # Step 2: x=2, y=5, w=1, z=2.
    # Seems logical z = step.
    # Fail: x=10, z=x.
    # At step 10: x=10. z=10.
    # Fail reached at step 10.
    # Trace length 11.
    
    x, y, z, w = 0, 1, 0, 1
    t_x, t_y, t_z, t_w = [], [], [], []
    for i in range(12):
        t_x.append(x); t_y.append(y); t_z.append(z); t_w.append(w)
        
        old_x, old_y, old_w, old_z = x, y, w, z
        x += 1
        y += 2
        w = 1 - w
        
        cond_val = (old_x + old_y) % 2
        if cond_val == old_w:
            z = old_z + 1
        else:
            z = 0
            
    generate_sygus_file("s_split_21_trace.sygus", 12,
                        {"fx": t_x, "fy": t_y, "fz": t_z, "fw": t_w},
                        None, None)

if __name__ == "__main__":
    simulate_05_and_21()
