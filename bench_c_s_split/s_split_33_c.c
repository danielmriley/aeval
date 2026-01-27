#include <assert.h>
extern int unknown1();
int main()
{
  int x=0;int y=0; int z=0;
  while(unknown1()) {
    x = x+1;
    if((z/100)==(x/100)) z=z;
    else z=z+100;
    y=(y+1)%100;
  }
  assert(!(x==z+y));
}
