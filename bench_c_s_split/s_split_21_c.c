#include <assert.h>
int main()
{
  int x=0; int y=1; int z=0; int w=1;
  while(x!=10) {
    if(((x+y)%2)==w) z=z+1;
    else z=0;
    x=x+1;
    y=y+2;
    w=1-w;
  }
  assert(!(x==z));
}
