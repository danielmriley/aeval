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
    uint8_t v2 = 0x00;

    while(1) {
        assert(!((v0 == 0xff)));

        // Transition
        uint8_t next_v0 = (v0 + 0x01);
        uint8_t next_v1 = (v1 + 0x02);
        uint8_t next_v2 = (v2 + 0x03);
        __CPROVER_assume((v0 < 0xff));

        // Update state
        v0 = next_v0;
        v1 = next_v1;
        v2 = next_v2;
    }
    return 0;
}
