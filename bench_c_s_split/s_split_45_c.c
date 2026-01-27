#include <assert.h>
extern int unknown1();
extern int unknown2();
int main()
{
  int x=0;int y=unknown1(); int z=unknown2();
  while(x<965552) {
    if(x>=765552){
      if(x>=865552)
        y=y;
      else
        y=y+1;
    }
    else y=0;
    if(x>=663258){
      if(x>=763258)
        z=z;
      else
        z=z+1;
    }
    else z=0;
    x++;
  }
  assert(!(y==z));
}
