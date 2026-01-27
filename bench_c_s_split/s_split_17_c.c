#include <assert.h>
extern int unknown1();
extern int unknown2();

int main()
{
  int x=unknown1(); int z=unknown2(); int v=0; int w=0;
  if(x<=z) return 0;
  while(v<=1000) {
    if(x<z) v=v+1;
    if(x<z) w=w;
    else w=w+1;
    x = x+1;
    z=z+2;
  }
  assert(!(w>0));
}
