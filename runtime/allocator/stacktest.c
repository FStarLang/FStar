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
#include <stdio.h>
#include <assert.h>
#include "stack.h"

static inline int align(int n, int blocksize) {
  return n % blocksize == 0 ? n : blocksize * ((n / blocksize) + 1);
}

static inline int word_align(int bytes) {
  return align(bytes,WORD_SZB);
}

#define WORDSIZE(t) (word_align(sizeof(t)) / WORD_SZB)

void printptrs(void *ign, void **ptr) {
  printf("  live pointer addr=%p, val=%p\n",ptr,*ptr);
}

typedef struct _triple {
  long x;
  long y;
  long z;
} Triple;

int mark_ptr = 1;

void foo(int n) {
  int *x;
  int *y;
  int *z;
  if (n == 0) {
    printf("ending at iteration %d\n",n);
    each_marked_pointer(printptrs,0);
    return;
  } else {
    if (n % 3 == 0) push_frame();
    if (mark_ptr) {
      x = stack_alloc_mask(WORDSIZE(int),1,0);
      y = stack_alloc_mask(WORDSIZE(int),1,0);
      z = stack_alloc_mask(WORDSIZE(int),1,0);
    } else {
      x = stack_alloc_mask(WORDSIZE(int),0);
      y = stack_alloc_mask(WORDSIZE(int),0);
      z = stack_alloc_mask(WORDSIZE(int),0);
    }
    *x = n;
    *y = n+1;
    *z = n+2;
    foo(n-1);
    assert(is_stack_pointer(x) && is_stack_pointer(y) && is_stack_pointer(z));
    assert(*x == n);
    assert(*y == n+1);
    assert(*z == n+2);
    if (n % 3 == 0) { 
      pop_frame();
      printf("popped frame after iteration %d\n",n);
      each_marked_pointer(printptrs,0);
      assert(!is_stack_pointer(x) && !is_stack_pointer(y) && !is_stack_pointer(z));
    }
  }
}

void bar(int n) {
  Triple *p;
  if (n == 0) {
    printf("ending at iteration %d\n",n);
    each_marked_pointer(printptrs,0);
    return;
  } else {
    if (n % 3 == 0) push_frame();
    if (mark_ptr) {
      p = stack_alloc_mask(WORDSIZE(Triple),2,0,1);
    } else {
      p = stack_alloc(WORDSIZE(Triple));
    }
    p->x = n;
    p->y = n+1;
    p->z = n+2;
    bar(n-1);
    assert(is_stack_pointer(&p->x) && is_stack_pointer(&p->y) && is_stack_pointer(&p->z));
    assert(p->x == n);
    assert(p->y == n+1);
    assert(p->z == n+2);
    if (n % 3 == 0) { 
      pop_frame();
      printf("popped frame after iteration %d\n",n);
      each_marked_pointer(printptrs,0);
      assert(!is_stack_pointer(&p->x) && !is_stack_pointer(&p->y) && !is_stack_pointer(&p->z));
    }
  }
}

int main(int argc, char *argv[]) {
  push_frame();
  bar(10);
  mark_ptr = 0;
  printf("===> redoing, with no marking\n");
  bar(10);
  pop_frame();
  return 0;
}
