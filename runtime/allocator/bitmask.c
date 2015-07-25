#include "bitmask.h"

/* See bitmask.h for explanations of the functions. */

void eachbit(unsigned char *map, int maxbit, bitfun f, void *env) {
  int i;
  int maplen = maxbit / 8;
  for (i = 0; i<maplen; i++) {
    int j, k = 1;
    unsigned char v = map[i];
    if (v == 0)  continue;
    for (j = 0; j<sizeof(unsigned char)*8; j++) {
      if ((v & k) == k)
	f(env,i*sizeof(unsigned char)*8 + j);
      k = k << 1;
    }
  }
  /* XXX: The last fraction of the mask; probably could do this
     with less code duplication ... */
  if ((maxbit % 8) != 0) {
    unsigned char v = map[maplen];
    int j, k = 1;
    if (v != 0) {
      for (j = 0; j<(maxbit % 8); j++) {
	if ((v & k) == k)
	  f(env, maplen*sizeof(unsigned char)*8 + j);
	k = k << 1;
      }    
    }
  }
}

void setbit(unsigned char *map, int bit) {
  unsigned char v = map[bit / 8];
  int idx = 1 << (bit % 8);
  map[bit / 8] = v | idx;
}

void unsetbit(unsigned char *map, int bit) {
  unsigned char v = map[bit / 8];
  int idx = (1 << (bit % 8)) ^ 0xff ;
  map[bit / 8] = v & idx;
}

void unsetbit_rng(unsigned char *map, int bit, int len) {
  /* XXX optimize this to not do it a bit at a time */
  int i;
  for (i=0; i<len; i++) 
    unsetbit(map,bit+i);
}

/* TEST

#include <stdio.h>

void printidx(void *ign, int idx) {
  printf("got %d\n",idx);
}

int main() {
  unsigned char x[4] = { 0,1,1,1 };
  unsigned char y[4] = { 1,0, 1, 0 };
  unsigned char z[4] = { 3,3,255,0 };
  setbit(x,9);
  unsetbit(x,16);
  //unsetbit_rng(z,0,2);
  eachbit(x,4*8,printidx,0);
  eachbit(y,4*8,printidx,0);
  eachbit(z,24,printidx,0);
  return 0;
}
 
*/
