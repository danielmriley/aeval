#include <assert.h>
extern int unknown1();
int main()
{
  int x=1; int z=0;
  while(unknown1()) {
    if(x%3 == 1) z=z+x;
    else z=z-x;
    x=-x;
  }
  assert(!(z>=0));
}
