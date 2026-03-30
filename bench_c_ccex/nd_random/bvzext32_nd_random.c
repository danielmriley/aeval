#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    uint32_t v0 = 0x00000000;

    while(1) {
        assert(!(!(((((unsigned long long)v0) + 0x0000000000000001) < 0x0000000100000000))));

        // Transition
        uint32_t next_v0;
        next_v0 = nondet_uint();

        // Update state
        v0 = next_v0;
    }
    return 0;
}
