#include <assert.h>
int main()
{
  int x=0; int y=0; int z=0; int w=0;
  while(x<=100) {
    if((y-(10*x))>0) z=z+1;
    if((y-(10*x))>0) w=w;
    else w=w+1;
    y=y+x;
    x = x+1;
  }
  assert(!(z>w));
}
