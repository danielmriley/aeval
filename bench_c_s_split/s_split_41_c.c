#include <assert.h>
int main()
{
  int x=0;int y=7500;
  while(x!=10000) {
    if(x>=5000) y=y+1;
    if(0==x%2) x=x+2;
    else x = x+1;
  }
  assert(!(y==10000));
}
