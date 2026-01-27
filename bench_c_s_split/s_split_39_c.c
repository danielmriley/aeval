#include <assert.h>
int main()
{
  int x=0;int z=0;
  while(z<=50) {
    if((x*5)<z) x=x+1;
    else x = x/10;
    if((x*5)<z) z=z;
    else z=z+1;
  }
  assert(!(z>x));
}
