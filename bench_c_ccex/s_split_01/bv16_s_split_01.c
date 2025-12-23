#include <assert.h>
#include <stdint.h>

// CBMC intrinsics
unsigned int nondet_uint();
unsigned char nondet_uchar();
unsigned short nondet_ushort();
unsigned long nondet_ulong();
void __CPROVER_assume(int);

int main() {
    uint16_t v0 = 0;
    uint16_t v1 = 5000;

    while(1) {

        // Transition
        uint16_t next_v0 = (v0 + 1);
        uint16_t next_v1 = ((v0 >= 5000) ? (v1 + 1) : v1);

        // Update state
        v0 = next_v0;
        v1 = next_v1;
    }
    return 0;
}
