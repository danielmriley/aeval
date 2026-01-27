#include <assert.h>
int main()
{
  int x=-100; int z=-100;
  while(z<0) {
    if(z<4) z=z+1;
    else z=z%4;
    x=++x;
    x=x%5;
  }
  assert(!(x==z));
}
