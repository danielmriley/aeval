
import sys

def to_hex(val, width=16):
    return f"#x{val:04x}"

def generate_sygus():
    # Simulation parameters
    limit = 10000 # 0x2710
    phase_threshold = 5000 # 0x1388
    
    # State initialization
    x = 0
    y = 5000 # 0x1388
    step = 0
    
    points = []
    
    # Simulate trace
    # We record state (step, x, y)
    while x <= limit:
        points.append((step, x, y))
        
        # Transition relation check logic
        next_y = y  # Default case: y doesn't change
        if x >= phase_threshold:
            next_y = (y + 1) & 0xFFFF
            
        y = next_y
        x = (x + 1) & 0xFFFF
        step += 1
        
    
    with open("s_split_experiment.sygus", "w") as f:
        f.write("(set-logic BV)\n")
        
        grammar = """
  ((Start (_ BitVec 16)) (MyBool Bool))
  ((Start (_ BitVec 16) (
    n
    #x0000
    #x0001
    #x1388
    (bvadd Start Start)
    (ite MyBool Start Start)
  ))
   (MyBool Bool (
     (bvuge n #x1388)
     (bvult n #x1388)
     (bvult Start Start)
   )))
"""

        # Synthesize function fx(n) -> x
        f.write("(synth-fun fx ((n (_ BitVec 16))) (_ BitVec 16)\n")
        f.write(grammar)
        f.write(")\n\n")

        # Synthesize function fy(n) -> y
        f.write("(synth-fun fy ((n (_ BitVec 16))) (_ BitVec 16)\n")
        f.write(grammar)
        f.write(")\n\n")
        
        # Constraints from trace
        for step_val, px, py in points:
            step_hex = to_hex(step_val)
            f.write(f"(constraint (= (fx {step_hex}) {to_hex(px)}))\n")
            f.write(f"(constraint (= (fy {step_hex}) {to_hex(py)}))\n")
            
        f.write("\n(check-synth)\n")

if __name__ == "__main__":
    generate_sygus()
