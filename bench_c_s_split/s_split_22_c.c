#include <assert.h>
int main()
{
  int x=0; int y=767976; int z=0;
  while(x<280275) {
    if((x-y)%3==1) z=z+3;
    x=x+1;
    y=y-1;
  }
  assert(!(z>=280275));
}
