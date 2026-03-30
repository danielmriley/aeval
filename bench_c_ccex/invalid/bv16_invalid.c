#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    uint16_t v0 = 0x0000;

    while(1) {
        assert(!((v0 == 0xffff)));

        // Transition
        uint16_t next_v0 = (v0 + 0x0001);
        __CPROVER_assume((v0 < 0xffff));

        // Update state
        v0 = next_v0;
    }
    return 0;
}
