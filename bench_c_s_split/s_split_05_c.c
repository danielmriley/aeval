#include <assert.h>
extern int unknown1();
extern int unknown2();
int main()
{
  int x=unknown1(); int y=unknown2(); int z = 1;
  if(x<=0) return 0;
  if(y>=0) return 0;
  while(y<x) {
    if(y>=0) z=z*2;
    x++;
    y=y+2;
  }
  assert(!(z>1));
}
