#include <assert.h>
extern int unknown1();
int main()
{
  int x=0;int y=unknown1(); int z=0;
  if(y<0) return 0;
  while(x>=(777*(10+y))) {
    if(x>=777*y){
      if(x>777*(y+5))
        z=z+1;
    }
    x++;
  }
  assert(!(z==3885));
}
