#include <assert.h>
int main()
{
  int x=0;int y=8000; int z=0;
  while(x!=16000) {
    if(x>=8000) y=y+1;
    else y=y-1;
    if(x<8000) z=z+1;
    else z=z-1;
    x=x+1;
  }
  assert(!(y==8000&&z==0));
}
