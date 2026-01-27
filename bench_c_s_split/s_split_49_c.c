#include <assert.h>
int main()
{
  int x=0;int y=0;
  while(x!=15000) {
    if(x>=7500){
      if(x>=12500)
        y=y-2;
      else
        y=y+1;
    }else{
      if(x>=2500)
        y=y+1;
      else
        y=y-2;
    }
    x++;
  }
  assert(!(y==0));
}
