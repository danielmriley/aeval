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
        assert(!(!((((((unsigned long long)v0) + 0x0001) < 0x0100) && ((((unsigned long long)v1) + 0x0001) < 0x0100)))));

        // Transition

        unsigned int choice = nondet_uint();
        if ((choice % 2) == 0) {
            v0 = (v0 + 0x01);
            v1 = v1;
        } else         if ((choice % 2) == 1) {
            v0 = v0;
            v1 = (v1 + 0x01);
        }
    }
    return 0;
}
