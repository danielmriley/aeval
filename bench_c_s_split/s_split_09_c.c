#include <assert.h>
int main()
{
  int x=0;
  while(x%4!=0) {
    if(x==9998) x=1;
    else x= x+2;
  }
  assert(!(x<=9996));
}
