#include <assert.h>
extern int unknown1();
int main()
{
  int x=0; int z=unknown1(); int w=0;
  if(z<=53736239) return 0;
  while(x<=z) {
    if(x<z||(x%2)==0) w=w+1;
    else w=w-1;
    x = x+1;
  }
  assert(!(w>=0));
}
