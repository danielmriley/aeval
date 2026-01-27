#include <assert.h>
int main()
{
  int x=50000;int y=0;
  while(y<=50000) {
    if(y>=x) x=x+5;
    if(y>=x) y=y;
    else y=y+1;
  }
  assert(!((x-y)<=5));
}
