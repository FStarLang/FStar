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
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <stdarg.h>
#include "stack.h"
#include "bitmask.h"

/* Utility routines */

#define check(_p) if (!(_p)) { fprintf(stderr,"Failed check %s:%d\n",__FILE__,__LINE__); fflush(stdout); exit(1); }
#define assert check
#define max(a,b) (a>b?a:b)

#define WORD_SZB sizeof(void*)

static inline int align(int n, int blocksize) {
  return n % blocksize == 0 ? n : blocksize * ((n / blocksize) + 1);
}

static inline int word_align(int bytes) {
  return align(bytes,WORD_SZB);
}

static inline int byte_align(int bits) {
  return align(bits,8);
}

/* 
   A stack is implemented as a list of pages, where the front of the list
   is the top of the stack. One page can store many frames and a frame
   can span multiple pages. Allocation is always word aligned.
*/

typedef struct _Page {
  void* memory; /* contains the memory for this page; returned by malloc() */
  void* alloc_ptr; /* the allocation pointer (within the page memory) */
  void* limit_ptr; /* the limit pointer (points to the end of memory) */
  void** frame_ptr; /* points to the base of the current frame, in the memory */
    /* frame_ptr == NULL implies this is the topmost frame of the current page */
    /* frame_ptr == EXT_MARKER implies this frame begins on the prior page */
    /* frame_ptr == p implies p points to the base of the frame in the page's memory */
  struct _Page *prev; /* points to the previous page on the stack */
  unsigned char pointermap[0]; /* contains a bitmask that identifies all pointers on this page. */
    /* this map is only valid for memory in the range [memory -- alloc_ptr]; outside
       that range it is garbage. Also, the map is at word granularity. */
} Page;

#define EXT_MARKER (void **)0x1

/* The top of the stack */
static Page *top = NULL;

/* [have_space(b)] returns 1 iff there exist [b] bytes available to allocate on the current page */
static inline int have_space(int sz_b) {
  return (((unsigned long)top->limit_ptr - (unsigned long)top->alloc_ptr) >= sz_b);
}

/* [add_page(b,e)] pushes a new page on the stack, where the page should have at least
   [b] bytes. If [e] is 1, then this page is extending a frame begun on the previous page.
   Otherwise the page coincides with the start of a new frame. */
static void add_page(int sz_b, int is_ext) {
  sz_b = word_align(max(2*sz_b,DEFAULT_PAGE_SZB));
  int mapsz_b = byte_align(sz_b/WORD_SZB)/8;
  Page *region = malloc(sizeof(Page)+mapsz_b);
  printf ("add page size = %d, ext = %d, map size = %d\n", sz_b, is_ext, mapsz_b);
  void* memory = malloc(sz_b);
  check (region != NULL);
  check (memory != NULL);
  region->memory = memory;
  region->alloc_ptr = memory;
  region->limit_ptr = (void *)((unsigned long)memory + (unsigned long)sz_b);
  region->frame_ptr = is_ext ? EXT_MARKER : NULL;
  region->prev = top;
  top = region;
}

/* [push_frame(b)] pushes a new frame on the stack. It attempts to add that
   frame to the current page, if there is space. In that case, it stores the current
   frame pointers at the allocation pointer, updates the frame pointer to point to
   that location, and then advances the allocation pointer (as in a C function call). 
   It also clears the pointermap for the frame pointer's storage. If insufficient
   space exists on the current page to support the frame, then a new page is 
   allocated, establishing the new frame. */
void push_frame(int sz_b) {
  assert(sz_b >= 0);  
  sz_b = word_align(sz_b);
  if (top != NULL && have_space(sz_b+sizeof(void*))) { // can continue with current page
    //printf("push frame in page\n");
    *((void **)top->alloc_ptr) = top->frame_ptr;
    top->frame_ptr = top->alloc_ptr;
    int bit = (void **)top->frame_ptr - (void **)top->memory; 
    unsetbit(top->pointermap, bit);
    top->alloc_ptr = (void *)((unsigned long)top->alloc_ptr + WORD_SZB);
  } else {
    //printf("push frame on new page\n");
    add_page(sz_b,0);
  }
}

int pop_frame() {
  if (top == NULL) return -1;
  if (top->frame_ptr != NULL && top->frame_ptr != EXT_MARKER) {
    //printf ("pop frame on page\n");
    top->alloc_ptr = top->frame_ptr;
    top->frame_ptr = *((void **)top->alloc_ptr);
  } else {
    Page *prev = top->prev;
    void **fp = top->frame_ptr;
    //printf ("pop frame and free page\n");
    //for debugging:
#ifndef NDEBUG
    memset(top->memory, 255, ((unsigned long)top->limit_ptr - (unsigned long)top->memory));
#endif
    free(top->memory);
    free(top);
    top = prev;
    if (fp == EXT_MARKER) {
      //printf ("recursively pop frame\n");
      pop_frame();
    }
  }
  return 0;
}

void *stack_alloc_maskp(int sz_b, int nbits, int *mask) {
  if (top == NULL) return NULL;
  sz_b = word_align(sz_b);
 retry: if (have_space(sz_b)) { // can continue with current page
    void *res = top->alloc_ptr;
    //printf("allocated %d bytes\n", sz_b);
    int ofs = (void **)res - (void **)top->memory; // #words into the page
    int i;
    top->alloc_ptr = (void *)((unsigned long)top->alloc_ptr + sz_b);
    unsetbit_rng(top->pointermap, ofs, sz_b / WORD_SZB);
    for (i = 0; i<nbits; i++) {
      setbit(top->pointermap, mask[i]+ofs);
    }
    return res;
  } else {
    //printf("adding page on demand\n");
    add_page(sz_b,1);
    goto retry;
  }
}

void *vstack_alloc_mask(int sz_b, int nbits, va_list argp) {
  int buf[256];
  int i;
  assert(nbits < 256);
  for (i=0; i<nbits; i++) {
    int n = va_arg(argp,int);
    buf[i] = n;
  }
  return stack_alloc_maskp(sz_b,nbits,buf);
}  

void *stack_alloc_mask(int sz_b, int nbits, ...) {
  va_list argp;
  void *result;
  va_start(argp, nbits);
  result = vstack_alloc_mask(sz_b, nbits, argp);
  va_end(argp);
  return result;
}

void *stack_alloc(int sz_b) {
  return stack_alloc_mask(sz_b, 0);
}

int is_stack_pointer(void *ptr) {
  Page *tmp = top;
  while (tmp != NULL) {
    if (tmp->memory <= ptr && tmp->alloc_ptr > ptr)
      return 1;
    tmp = tmp->prev;
  }
  return 0;
}

// running a callback on each marked word
struct ptrenv { 
  void **memory; 
  ptrfun f;
  void *env;
};

void ptrbitfun(void *env, int index) {
  struct ptrenv *penv = (struct ptrenv *)env;
  void **ptr = &(penv->memory[index]);
  penv->f(penv->env,ptr);
}

void each_marked_pointer(ptrfun f, void *env) {
  Page *tmp = top;
  struct ptrenv penv = { 0, f, env };
  while (tmp != NULL) {
    int maxbit = (void **)tmp->alloc_ptr - (void **)tmp->memory; 
    penv.memory = (void**)tmp->memory;
    eachbit(tmp->pointermap, maxbit, ptrbitfun, (void *)&penv);
    tmp = tmp->prev;
  }
}
