#include <assert.h>
extern int unknown1();
int main()
{
  int x=0;int y=unknown1(); int z=y;
  if(y<=x) return 0;
  while(x<=2*y) {
    if(x<y) z=z-1;
    else {
      if(z<y) z++;
    }
    x++;
  }
  assert(!(y==z));
}
