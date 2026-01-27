#include <assert.h>
extern int unknown1();
extern int unknown2();
int main()
{
  int x=0;int y=unknown1(); int z=unknown2(); int w=0;
  if(y<=z) return 0;
  while(x<=y) {
    if(x<z) w=w+1;
    else w = w-1;
    x = x+5;
    y=y+3;
    z=z+1;
  }
  assert(!(w<=0));
}
