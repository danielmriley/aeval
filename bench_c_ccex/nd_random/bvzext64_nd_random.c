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

    while(1) {

        // Transition
        uint64_t next_v0;
        next_v0 = nondet_ulong();

        // Update state
        v0 = next_v0;
    }
    return 0;
}
