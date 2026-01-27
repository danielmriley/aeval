#include <assert.h>
extern int unknown1();
int main()
{
  int x=0; int y=10; int z=0;
  while(unknown1()) {
    if(x==y) z=0;
    else z++;
    x = (x+1)%10;
    y = (y-1)%10;
  }
  assert(!(z<=5));
}
