#include <assert.h>
int main()
{
  int x=0;int y=0; int z=0; int w=500;
  while(y!=2250) {
    if(x<500) z=z+1;
    else z=z-1;
    if(x>=500) w=w+1;
    else w=w-1;
    x=(x+1)%1000;
    y=y+1;
  }
  assert(!(z==w));
}
