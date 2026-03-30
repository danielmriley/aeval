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

        unsigned int choice = nondet_uint();
        if ((choice % 2) == 0) {
            v0 = (v0 + 0x00000001);
            v1 = v1;
        } else         if ((choice % 2) == 1) {
            v0 = v0;
            v1 = (v1 + 0x00000001);
        }
    }
    return 0;
}
