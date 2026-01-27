#include <assert.h>
int main()
{
  int x=0;int y=1000; int z=2000; int w=3000;
  while(z<3000) {
    if(z>=3000) w=w+1;
    if(y>=2000) z=z+1;
    if(x>=1000) y=y+1;
    x++;
  }
  assert(!(x==w));
}
