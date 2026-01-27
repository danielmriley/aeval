#include <assert.h>
int main()
{
  int x=1; int y=1;
  while(x<=16) {
    if(y<16) y=y*2;
    else y=x%16;
    x = x*2;
  }
  assert(!(y==0));
}
