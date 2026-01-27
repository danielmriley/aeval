#include <assert.h>
int main()
{
  int x=0;int c=5000; int y=c;
  while(x!=2*c) {
    int tx=x+1;
    int ty=y-1;
    if(x>=c) y=y+1;
    else y=y-1;
    x=x+1;
  }
  assert(!(y==c));
}
