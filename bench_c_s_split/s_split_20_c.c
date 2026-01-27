#include <assert.h>
int main()
{
  int x=0; int y=0; int z=-1;
  while(x!=942573485) {
    if(x%2==0) z=z+1;
    x = x+1;
    y=-1*(y+x);
  }
  assert(!((y+z)==0));
}
