#include <assert.h>
int main()
{
  int x=52; int y=97; int z=-76; int w=0;
  while(y<80914) {
    z=(-5*x)+(3*y)+(4*z)-8754;
    if(z>0) w=w-x;
    x = 13-(7*x);
    y=54-(2*y);
  }
  assert(!(w>0));
}
