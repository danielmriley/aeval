#include <assert.h>
extern int unknown1();
extern int unknown2();
int main()
{
  int x=0; int y=unknown1(); int z =unknown2(); int w=0;
  if(y<=z) return 0;
  while(x<=(y+z)) {
    if(x<z) w=w+1;
    else w=w-2;
    x++;
  }
  assert(!(w<=0));
}
