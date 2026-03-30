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
    uint32_t v1 = 0x00000000;

    while(1) {
        assert(!(!((((((unsigned long long)v0) + 0x0000000000000001) < 0x0000000100000000) && ((((unsigned long long)v1) + 0x0000000000000001) < 0x0000000100000000)))));

        // Transition
        uint32_t next_v0 = (v0 + 0x00000001);
        uint32_t next_v1;
        next_v1 = nondet_uint();
        __CPROVER_assume(((v0 >= 0x80000000) ? (next_v1 == (v1 + 0x00000001)) : (next_v1 == v1)));

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
