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
#include "stack.h"

#define check(_p) if (!(_p)) { fprintf(stderr,"Failed check %s:%d\n",__FILE__,__LINE__); fflush(stdout); exit(1); }
#define assert check
#define max(a,b) (a>b?a:b)

#define WORD_SZB sizeof(void*)

//a stack of pages represented as a linked list with downward (popward) links 
// One page can store many F* stack frames. One F* stack frame can span many pages?
typedef struct _Page {
  void* memory; // returned by malloc. the region between thiz.memory and this.limit_ptr can be used for storing client's data
  void* alloc_ptr; // the absolute position within this.memory where the next allocation will happen
  void* limit_ptr;
  void** frame_ptr; //location of frame pointer?
  struct _Page *prev;
} Page;

#define EXT_MARKER (void **)0x1

/* INVARIANTS:
   frame_ptr == NULL || frame_ptr == EXT_MARKER || location of stored frameptr
 */

static Page *top = NULL;

static inline int word_align(int sz_b) {
  return sz_b % WORD_SZB == 0 ? sz_b : WORD_SZB * ((sz_b / WORD_SZB) + 1);
}

static inline int have_space(int sz_b) {
  return (((unsigned long)top->limit_ptr - (unsigned long)top->alloc_ptr) >= sz_b);
}

static void add_page(int sz_b, int is_ext) {
    Page *region = malloc(sizeof(Page));
    sz_b = max(2*sz_b,DEFAULT_PAGE_SZB);
    //printf ("add page size = %d, ext = %d\n", sz_b, is_ext);
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

void push_frame(int sz_b) {
  sz_b = word_align(sz_b);
  if (top != NULL && have_space(sz_b+sizeof(void*))) { // can continue with current region
    //printf("push frame in page\n");
    *((void **)top->alloc_ptr) = top->frame_ptr;
    top->frame_ptr = top->alloc_ptr;
    top->alloc_ptr = (void *)((unsigned long)top->alloc_ptr + WORD_SZB);
  } else {
    //printf("push frame on new page\n");
    add_page(sz_b,0);
  }
}

void pop_frame() {
  if (top->frame_ptr != NULL && top->frame_ptr != EXT_MARKER) {
    //printf ("pop frame on page\n");
    top->alloc_ptr = top->frame_ptr;
    top->frame_ptr = *((void **)top->alloc_ptr);
  } else {
    Page *prev = top->prev;
    void **fp = top->frame_ptr;
    //printf ("pop frame and free page\n");
    //for debugging:
    //memset(top->memory, 255, ((unsigned long)top->limit_ptr - (unsigned long)top->memory));
    free(top->memory);
    free(top);
    top = prev;
    if (fp == EXT_MARKER) {
      //printf ("recursively pop frame\n");
      pop_frame();
    }
  }
}

void *stack_alloc(int sz_b) {
  assert(top != NULL);
  sz_b = word_align(sz_b);
 retry: if (have_space(sz_b)) { // can continue with current region
    void *res = top->alloc_ptr;
    //printf("allocated %d bytes\n", sz_b);
    top->alloc_ptr = (void *)((unsigned long)top->alloc_ptr + sz_b);
    return res;
  } else {
    //printf("adding page on demand\n");
    add_page(sz_b,1);
    goto retry;
  }
}
