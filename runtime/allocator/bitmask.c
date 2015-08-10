/*
   Copyright 2015 Michael Hicks, Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

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
  int m = 1 << (bit % 8);
  map[bit / 8] = v | m;
}

void unsetbit(unsigned char *map, int bit) {
  unsigned char v = map[bit / 8];
  int m = (1 << (bit % 8)) ^ 0xff ;
  map[bit / 8] = v & m;
}

#define MIN(x,y) (x) < (y) ? (x) : (y)

void unsetbit_rng(unsigned char *map, int bit, int len) {
  /* up to first byte boundary */
  if (bit % 8 != 0) {
    int i; /* XXX: create the mask all at once */
    int l = MIN(8-(bit % 8), len);
    for (i=0; i<l; i++) 
      unsetbit(map,bit+i);
    bit += l;
    len -= l;
  }
  /* series of bytes */
  while (len >= 8) {
    map[bit / 8] = (unsigned char)0;
    len -= 8; 
    bit += 8;
  }
  /* last fractional byte */
  if (len > 0) {
    unsigned char v = map[bit / 8];
    int m = 0xff ^ ((1 << len) - 1);
    map[bit / 8] = v & m;
  }
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

  printf ("x:\n");
  setbit(x,9);
  unsetbit(x,16);
  eachbit(x,4*8,printidx,0);

  printf ("y:\n");
  eachbit(y,4*8,printidx,0);

  printf ("z:\n");
  unsetbit_rng(z,8,12);
  eachbit(z,24,printidx,0);
  return 0;
}
 
*/
