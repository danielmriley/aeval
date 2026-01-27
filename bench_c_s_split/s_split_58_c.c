#include <assert.h>
extern int unknown1();
int main()
{
  int x=0; int y=unknown1(); int z=0;
  while(x<=(100*(y+1))) {
    if(y==(x/100)) z=z+1;
    x = x+1;
  }
  assert(!(z==100 && y>=0));
}
