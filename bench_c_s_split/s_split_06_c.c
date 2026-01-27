#include <assert.h>
int main()
{
  int x=1; int y=0; int z=0;
  while(y!=342341341) {
    if(x>0) y=y+1;
    if(x>0) z=z;
    else z=z+1;
    x=-x;
  }
  assert(!(z==342341341));
}
