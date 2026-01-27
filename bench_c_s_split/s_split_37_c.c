#include <assert.h>
int main()
{
  int x=0;int y=0; int z=0;
  while(x<10) {
    if(x==0) y=523;
    else y=y+z;
    if(x==0) z=z;
    else z=250;
    x++;
  }
  assert(!(y>2500));
}
