#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    uint64_t v0 = 0x0000000000000000;
    uint64_t v1 = 0x0000000000000000;

    while(1) {

        // Transition
        uint64_t next_v0 = (v0 + 0x0000000000000001);
        uint64_t next_v1;
        next_v1 = nondet_ulong();
        __CPROVER_assume(((v0 >= 0x8000000000000000) ? (next_v1 == (v1 + 0x0000000000000001)) : (next_v1 == v1)));

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
