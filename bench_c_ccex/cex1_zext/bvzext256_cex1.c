#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    unsigned __int128 v0 = 0x0000000000000000000000000000000000000000000000000000000000000000;

    while(1) {

        // Transition
        v0 = (v0 + 0x0000000000000000000000000000000000000000000000000000000000000001);
    }
    return 0;
}
