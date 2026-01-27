#include <assert.h>
extern int unknown1();
extern int unknown2();
extern int unknown2();
int main()
{
  int x=unknown1(); int y=unknown2(); int z =unknown3(); int v=0;
  if(x<=y) return 0;
  if(y<=z) return 0;
  while((z-x)<=72531) {
    if(x<y) v=v+1;
    x++;
    y=y+3;
    z=z+2;
  }
  assert(!(v>0));
}
