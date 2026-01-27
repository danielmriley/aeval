#include <assert.h>
int main()
{
  int x=0;int y=0;int z=0;
  while(x<=100) {
    if(x>100||(x%10)<5) y=y+1;
    if(x>100||(x%10)<5) z=z;
    else z=z+1;
    x++;
  }
  assert(!(y>z));
}
