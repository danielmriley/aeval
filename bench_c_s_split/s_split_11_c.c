#include <assert.h>
extern int unknown1();
extern int unknown2();
extern int unknown3();
int main()
{
  int x=unknown1(); int y=unknown2(); int z=unknown3();
  if(x>=0) return 0;
  if(y <= x) return 0;
  if(z!=0 && z!=1) return 0;
  while(x<=54932) {
    if(x%2==z) y=y+2;
    x++;
  }
  assert(!(y>54932));
}
