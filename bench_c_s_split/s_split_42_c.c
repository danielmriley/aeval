#include <assert.h>
int main()
{
  int x=0;int y=0; int z=0;
  while(x<=17650) {
    if(x>=1765) y=y+2;
    else y=y+1;
    if(y>=5765) z=z+3;
    else z=z+2;
  }
  assert(!(z>27650));
}
