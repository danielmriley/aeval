#include <assert.h>
int main()
{
  int x=-10000;int y=0;
  while(x<0) {
    if(y>=x) x=x+1;
    if(y>=x) y=-1 * x;
    else y=y+2;
  }
  assert(!(x>=(y-1)));
}
