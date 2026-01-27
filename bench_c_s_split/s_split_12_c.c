#include <assert.h>
int main()
{
  int x=0; int y=0; int z=0;
  while(x!=1342342) {
    if(x%2 == 0) y=y+1;
    if(x%2 == 0) z=z;
    else z++;
    x++;
  }
  assert(!(y==z));
}
