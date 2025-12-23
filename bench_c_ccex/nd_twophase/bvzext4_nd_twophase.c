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

        // Transition
        uint8_t next_v0 = (v0 + 0x1);
        uint8_t next_v1;
        next_v1 = nondet_uchar();
        __CPROVER_assume(((v0 >= 0x8) ? (next_v1 == (v1 + 0x1)) : (next_v1 == v1)));

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
