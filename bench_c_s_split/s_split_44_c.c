#include <assert.h>
int main()
{
  int x=0;int y=1000; int z=2000;
  while(y<2000) {
    if(y>=2000) z=z+1;
    if(x>=1000) y=y+1;
    x=x+1;
  }
  assert(!(x==z));
}
