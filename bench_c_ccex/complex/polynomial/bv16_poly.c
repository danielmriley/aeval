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
    uint16_t v1 = 0x0000;

    while(1) {
        assert(!((v1 == 0xfe01)));

        // Transition
        uint16_t next_v0 = (v0 + 0x0001);
        uint16_t next_v1 = (v1 + ((0x0002 * v0) + 0x0001));

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
