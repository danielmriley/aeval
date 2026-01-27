#include <assert.h>
int main()
{
  int x=0;int y=0; int z=0; int w=0;
  while(y!=999000) {
    if(x<1000) z=z+1;
    if(x>=1000) w=w+1;
    x=(x+1)%2000;
    y=y+1;
  }
  assert(!(1000==z-w));
}
