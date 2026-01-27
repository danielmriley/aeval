#include <assert.h>
void main()
{
  int x=0; int y=5000;
  while(x!=10000) {
    if(x>=5000) y++;
    x++;
  }
  assert(!(y==x));
}
