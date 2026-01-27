#include <assert.h>
int main()
{
  int x=0;int y=3333; int z=6666;
  while(x!=-9999) {
    if(y>=6666) z=z+1;
    if(x<3333) y=y;
    else y=y+1;
    x=x+1;
  }
  assert(!(z==x));
}
