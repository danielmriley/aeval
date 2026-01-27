#include <assert.h>
extern int unknown1();
int main()
{
  int x=0; int y=unknown1(); int z=0;
  if(y<100) return 0;
  while(y!=0) {
    if(y<=(x/50)) z=z+1;
    x = x+1;
    y=y-1;
  }
  assert(!(z>0));
}
