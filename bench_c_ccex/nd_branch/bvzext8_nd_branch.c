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
        assert(!(!(((((unsigned long long)v0) + 0x0001) < 0x0100))));

        // Transition

        unsigned int choice = nondet_uint();
        if ((choice % 2) == 0) {
            if ((((v0 >> 0) & 1) == 0)) {
                v0 = (v0 + 0x01);
            }
        } else         if ((choice % 2) == 1) {
            if ((((v0 >> 0) & 1) == 1)) {
                v0 = (v0 + 0x02);
            }
        }
    }
    return 0;
}
