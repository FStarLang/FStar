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
#ifndef _STACK_H_
#define _STACK_H_

#include <stdarg.h>

/* Default size of contiguous memory in a frame */
#define WORD_SZB sizeof(void*)
#define DEFAULT_PAGE_SZB 8192
#define MIN_FRAME_SZB WORD_SZB*4

/* Creates a logical frame having at MIN_FRAME_SZB bytes. */
void push_frame(void);

/* Pops off the top frame, freeing the memory if the page is empty.
   Asumes the stack is non-empty. */
void pop_frame(void);

/* Allocates sz_b bytes on the topmost frame. Will add new pages as
   needed. Assumes the stack is non-empty. */
void *stack_alloc(int sz_b);

/* Allocates sz_b bytes on the topmost frame. Will add new pages as
   needed. Sets the bitmask at word-sized offsets given by the varargs. 
   If nbits is -1, then all words allocated are considered potentially
   pointerful. */
void *stack_alloc_mask(int sz_b, int nbits, ...);
void *vstack_alloc_mask(int sz_b, int nbits, va_list argp);
void *stack_alloc_maskp(int sz_b, int nbits, int *mask);

/* Returns 1 if the given pointer is one managed by the stack; 
   0 otherwise. */
int is_stack_pointer(void *ptr);

/* Executes the ptrfun on each marked word in the stack.
   The function receives the address of the marked word */
typedef void (*ptrfun)(void *env, void **ptr);
void each_marked_pointer(ptrfun f, void *env);

#endif
