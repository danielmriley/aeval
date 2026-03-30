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
        assert(!(!((((((unsigned long long)v0) + 0x01) < 0x10) && ((((unsigned long long)v1) + 0x02) < 0x10)))));

        // Transition
        v0 = (v0 + 0x1);
        v1 = (v1 + 0x2);
    }
    return 0;
}
