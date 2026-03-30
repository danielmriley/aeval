#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    uint8_t v0 = 0x00;
    uint8_t v1 = 0x00;

    while(1) {
        assert(!((v1 == 0x01)));

        // Transition
        uint8_t next_v0 = (v0 + 0x01);
        uint8_t next_v1;
        next_v1 = nondet_uchar();
        __CPROVER_assume(((v0 < 0xff) && (next_v1 == (((next_v0 & 0x01) == 0x00) ? next_v0 : (uint8_t)(0u - (uint8_t)(next_v0))))));

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
