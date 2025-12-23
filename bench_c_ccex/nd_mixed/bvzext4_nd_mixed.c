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

    while(1) {

        // Transition

        unsigned int choice = nondet_uint();
        if ((choice % 2) == 0) {
            v0 = (v0 + 0x1);
        } else         if ((choice % 2) == 1) {
            if (1) {
            }
        }
    }
    return 0;
}
