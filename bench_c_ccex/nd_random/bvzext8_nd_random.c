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

    while(1) {

        // Transition
        uint8_t next_v0;
        next_v0 = nondet_uchar();

        // Update state
        v0 = next_v0;
    }
    return 0;
}
