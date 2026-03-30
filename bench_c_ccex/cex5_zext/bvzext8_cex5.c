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
        assert(!(!((((((unsigned long long)v0) + 0x0001) < 0x0100) && ((((unsigned long long)v1) + 0x0002) < 0x0100)))));

        // Transition
        v0 = (v0 + 0x01);
        v1 = (v1 + 0x02);
    }
    return 0;
}
