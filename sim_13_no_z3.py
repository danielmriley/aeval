
def simulate_s_split_13():
    # Hardcoded simulation of s_split_13 logic
    # Logic from bv16_s_split_13.smt2
    
    # 16-bit signed integers
    def to_signed(n):
        n = n & 0xFFFF
        return n | (-(n & 0x8000))

    # Init: x=1, z=0
    x, z = 1, 0
    trace = [(0, x, z)]
    
    print(f"Start: x={x}, z={z}")
    
    # Fail condition: z >= 0
    # Original benchmark s_split_13.smt2 likely had (not (< z 0)) as fail.
    # Our fixed version has (bvsge z 0) -> Fail if z >= 0.
    # Since z starts at 0, it fails immediately.
    
    if z >= 0:
        print("Fail condition (z>=0) met at step 0.")
        return trace
        
simulate_s_split_13()
