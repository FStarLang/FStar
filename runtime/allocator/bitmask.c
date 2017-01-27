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

void eachbit(MASK_TYPE *map, int maxbit, bitfun f, void *env) {
  int i;
  int maplen = maxbit / BITS_PER_ELEM;
  for (i = 0; i<maplen; i++) {
    int j, k = 1;
    MASK_TYPE v = map[i];
    if (v == 0)  continue; /* no marked bits */
    if (v == (MASK_TYPE)-1) { /* all bits marked */
      for (j = 0; j<BITS_PER_ELEM; j++)
	f(env,i*BITS_PER_ELEM + j);
    } else { /* some bits marked */
      for (j = 0; j<BITS_PER_ELEM; j++) {
	if ((v & k) == k)
	  f(env,i*BITS_PER_ELEM + j);
	k = k << 1;
      }
    }
  }
  /* XXX: The last fraction of the mask; probably could do this
     with less code duplication ... */
  if ((maxbit % BITS_PER_ELEM) != 0) {
    MASK_TYPE v = map[maplen];
    int j, k = 1;
    if (v != 0) {
      for (j = 0; j<(maxbit % BITS_PER_ELEM); j++) {
	if ((v & k) == k)
	  f(env, maplen*BITS_PER_ELEM + j);
	k = k << 1;
      }    
    }
  }
}

void setbit(MASK_TYPE *map, int bit) {
  MASK_TYPE v = map[bit / BITS_PER_ELEM];
  int m = 1 << (bit % BITS_PER_ELEM);
  map[bit / BITS_PER_ELEM] = v | m;
}

void unsetbit(MASK_TYPE *map, int bit) {
  MASK_TYPE v = map[bit / BITS_PER_ELEM];
  int m = (1 << (bit % BITS_PER_ELEM)) ^ ((MASK_TYPE)-1) ;
  map[bit / BITS_PER_ELEM] = v & m;
}

#define MIN(x,y) (x) < (y) ? (x) : (y)

void unsetbit_rng(MASK_TYPE *map, int bit, int len) {
  /* up to first byte boundary */
  if (bit % BITS_PER_ELEM != 0) {
    int i; /* XXX: create the mask all at once */
    int l = MIN(BITS_PER_ELEM-(bit % BITS_PER_ELEM), len);
    for (i=0; i<l; i++) 
      unsetbit(map,bit+i);
    bit += l;
    len -= l;
  }
  /* series of bytes */
  while (len >= BITS_PER_ELEM) {
    map[bit / BITS_PER_ELEM] = (MASK_TYPE)0;
    len -= BITS_PER_ELEM; 
    bit += BITS_PER_ELEM;
  }
  /* last fractional byte */
  if (len > 0) {
    MASK_TYPE v = map[bit / BITS_PER_ELEM];
    int m = ((MASK_TYPE)-1) ^ ((1 << len) - 1); 
    map[bit / BITS_PER_ELEM] = v & m;
  }
}

void setbit_rng(MASK_TYPE *map, int bit, int len) {
  /* up to first byte boundary */
  if (bit % BITS_PER_ELEM != 0) {
    int i; /* XXX: create the mask all at once */
    int l = MIN(BITS_PER_ELEM-(bit % BITS_PER_ELEM), len);
    for (i=0; i<l; i++) 
      setbit(map,bit+i);
    bit += l;
    len -= l;
  }
  /* series of bytes */
  while (len >= BITS_PER_ELEM) {
    map[bit / BITS_PER_ELEM] = (MASK_TYPE)-1;
    len -= BITS_PER_ELEM; 
    bit += BITS_PER_ELEM;
  }
  /* last fractional byte */
  if (len > 0) {
    MASK_TYPE v = map[bit / BITS_PER_ELEM];
    int m = ((MASK_TYPE)1 << len) - 1; 
    map[bit / BITS_PER_ELEM] = v | m;
  }
}

/* TEST 
#include <stdio.h>

void printidx(void *ign, int idx) {
  printf("got %d\n",idx);
}

int main() {
  unsigned int x[5];

  unsetbit_rng(x,0,5*BITS_PER_ELEM);

  printf ("x:\n");
  setbit(x,1);
  setbit(x,8);
  setbit(x,9);
  setbit(x,10);
  setbit(x,33);
  setbit(x,34);
  setbit(x,73);
  setbit_rng(x,62,70);
  eachbit(x,150,printidx,0); 
  unsetbit_rng(x,9,70);
  eachbit(x,150,printidx,0); 
  return 0;
}
*/
