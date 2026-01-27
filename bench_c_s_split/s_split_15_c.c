#include <assert.h>
int main()
{
  int x=0; int y=0; int z=0;
  do{
    if(x<500) z=z+2;
    x++;
    x=x%1000;
    y++;
  }while(x!=0);
  assert(!(y==z));
}
