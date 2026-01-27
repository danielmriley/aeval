#include <assert.h>
extern int unknown1();
int main()
{
  int x=0;int y=0; int z=unknown1();
  if(z==0) return 0;
  while(x!=200) {
    if(z>0) y++;
    else y=y-2;
    if(x==100) z=-z;
    x++;
  }
  assert(!(y<=0));
}
