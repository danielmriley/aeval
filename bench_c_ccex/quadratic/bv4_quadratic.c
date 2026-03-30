#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    uint8_t v0 = 0x0;
    uint8_t v1 = 0x0;

    while(1) {
        assert(!((v1 == 0xC)));

        // Transition — mask to 4 bits to match (_ BitVec 4) SMT2 semantics
        uint8_t next_v0 = (v0 + 0x1) & 0xF;
        uint8_t next_v1 = (v1 + v0) & 0xF;

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
