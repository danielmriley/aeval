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
        assert(!(!(((v0 < 0x1) && (v1 < 0x1)))));

        // Transition
        v0 = (v0 + 0x1);
        v1 = (v1 + 0x1);
    }
    return 0;
}
