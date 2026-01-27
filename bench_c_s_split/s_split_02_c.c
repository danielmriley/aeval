#include <assert.h>

int main()
{
  int x=0; int y=200; int z =400;
  while(y<400) {
    if(x<200) y++;
    if(x<200) z=z;
    else z = z+2;
    x++;
  }
  assert(!(z==(2*x)));
}
