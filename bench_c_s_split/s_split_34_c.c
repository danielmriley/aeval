#include <assert.h>
extern int unknown1();
int main()
{
  int x=0;int y=1;
  while(unknown1()) {
    x = x+y;
    if((x>-100)&&(x<100)) y=y;
    else y=-y;
  }
  assert(!(x>=-100 && x<=100));
}
