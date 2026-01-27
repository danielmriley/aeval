#include <assert.h>
int main()
{
  int x=0;int y=0;
  while(x<100000000) {
    if(x>=50000000){
      if(x>=100000000)
        y=y;
      else
        y=y+1;
    }
    else y=0;
    x++;
  }
  assert(!(y=50000000));
}
