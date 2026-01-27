#include <assert.h>
int main()
{
  int x=0;
  while(x<2000) {
    if(x/5<200) x=x+1;
    else x=x+5;
  }
  assert(!(x%5==0));
}
