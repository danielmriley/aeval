#include <assert.h>
int main()
{
  int x=0; int y=0; int z =0;
  while(x<3452365) {
    if(y>x) z=z+1;
    y=x+y;
    x++;
  }
  assert(!(z>0));
}
