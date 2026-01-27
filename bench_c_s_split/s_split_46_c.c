#include <assert.h>
extern int unknown1();
int main()
{
  int x=0;int y=unknown1();
  while(x<2000) {
    if(x/5<200) x=x+1;
    else x=x+5;
    if(x==1000) y=0;
  }
  assert(!(y==0));
}
