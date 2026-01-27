#include <assert.h>
int main()
{
  int x=0;int y=0;
  while(x!=10000) {
    if(x<5000){
      if(x>=4000)
        y=y+4;
      else
        y=y+1;
    }
    else{
      if(x>=6000)
        y=y-1;
      else
        y=y-4;
    }
    x++;
  }
  assert(!(y==0));
}
