#include <assert.h>
extern int unknown1();
extern int unknown2();
int main()
{
  int x=unknown1();int y=0; int z=unknown2(); int w=1;
  if(z!=0&&z!=1) return 0;
  if(x!=z) return 0;
  while(x<=10) {
    if(z==x%2) w=w+y;
    else w=w-1;
    y=y+x-3;
    x = x+1;
    z=z-1;
  }
  assert(!(w>=0));
}
