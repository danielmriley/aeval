#include <assert.h>
int main()
{
  int x=1; int z=-1;
  while(x<=5143523){
    if(x<0) z=4*z;
    x = -1*(x+x);
  }
  assert(!((x+z)==0));
}
