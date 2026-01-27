#include <assert.h>
extern int unknown1();
extern int unknown2();
int main()
{
  int x=unknown1(); int y=unknown2(); int z=0;
  if(x!=0&&x!=1) return 0;
  if(y!=0&&y!=1) return 0;
  while(x<=400) {
    if((x%2)==(y%2)) z=z+1;
    x = x+2;
    y = y+3;
  }
  assert(!(z>=100));
}
