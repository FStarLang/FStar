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
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include "stack.h"
#include "camlstack.h"

#ifdef DEBUG
#define check(_p) if (!(_p)) { fprintf(stderr,"Failed check %s:%d\n",__FILE__,__LINE__); fflush(stdout); exit(1); }
#define Assert check
#else
#define Assert(_p)
#endif

/***********************************************************************/
/* Allocating OCaml values on the stack */
/***********************************************************************/

/*
   Caml run-tme information -- this is copied from run-time files.
   If these files change, or the representation of Caml values changes,
   then this file won't work.

   This was tested with OCaml 4.02.1
*/

//#include <caml/gc.h> /* The below is copied from this file */
#define Caml_black (3 << 8)
/* This depends on the layout of the header.  See [mlvalues.h]. */
#define Make_header(wosize, tag, color)                                       \
      (/*Assert ((wosize) <= Max_wosize),*/                                   \
       ((header_t) (((header_t) (wosize) << 10)                               \
                    + (color)                                                 \
                    + (tag_t) (tag)))                                         \
      )
//#include <caml/roots.h> /* The below is copied from this file */
typedef void (*scanning_action) (value, value *);
extern void (*caml_scan_roots_hook) (scanning_action);

/*
  The following routines that follow are based on the routines from
  the OCaml run-time system, in particular byterun/alloc.c. In
  particular,

  stack_caml_alloc is based on caml_alloc_small
  stack_caml_alloc_string is based on caml_alloc_string
  stack_caml_alloc_tuple is based on caml_alloc_tuple

  Inherent in these routines are assumptions made by the run-time
  system about how Caml values are laid out, and invariants about
  their contents. Changes to the run-time may break the routines.

  Both stack_caml_alloc and stack_caml_alloc_tuple have two
  additional arguments, defining the "pointer mask" for the
  to-be-allocated objects, needed to inform the GC.
 */


/* [stack_caml_alloc s t n m] allocates an OCaml value that is [s]
   words in length and has OCaml tag [t]. There are [n] words among
   the [s] allocated that will contain pointers, once the value is
   initialized. Which pointers are defined by offset, in [m]. (If [n]
   is set to -1, then all words will be deemed as potentially
   pointerful, regardless of the contents of [m].) That is, [m] is an
   integer array of length (at least) [n], and each element of the
   array indicates the offset of the word in the allocated memory that
   will contain an allocated pointer. IMPORTANT: these offsets begin
   at 1, not 0.  As an example, suppose we wanted to allocate a pair
   of values, where the second one is a pointer to the OCaml
   heap. Then the call might be [stack_caml_alloc(2,0,1,m)] where [m]
   is an array of length 1, and its single element is the integer 2.
 */
value stack_caml_alloc(mlsize_t wosize, tag_t tag, int nbits, int *mask) {
  value tmp, result;
  Assert (tag < 256);
  Assert (tag != Infix_tag);
  Assert (wosize != 0);
  /*The provided mask indexes words starting at 1 so as to skip over
    the header word. */
  tmp = (value)stack_alloc_maskp(Whsize_wosize(wosize),nbits,mask);
#ifdef DEBUG
  if (tmp == (value)0) return tmp;
#endif
  Hd_hp (tmp) = Make_header (wosize, tag, Caml_black);
  result = Val_hp (tmp);
  return result;
}

/* [stack_caml_alloc_string n] allocates an uninitialized Caml string
   of length [n]. */
value stack_caml_alloc_string (mlsize_t lenb)
{
  /* FYI: http://caml.inria.fr/pub/ml-archives/caml-list/2002/08/e109df224ff0150b302033e2002dbf87.en.html */
  value result;
  mlsize_t offset_index;
  mlsize_t wosize = (lenb + sizeof (value)) / sizeof (value);
  result = stack_caml_alloc (wosize, String_tag, 0, NULL);
#ifdef DEBUG
  if (result == (value)0) return result;
#endif
  Field (result, wosize - 1) = 0;
  offset_index = Bsize_wsize (wosize) - 1;
  Byte (result, offset_index) = offset_index - lenb;
  return result;
}

value stack_concat (value s1, value s2) {
  mlsize_t l1 = caml_string_length (s1);
  mlsize_t l2 = caml_string_length (s2);
  value s = stack_caml_alloc_string (l1 + l2);
  if (s == (value)0)
    caml_failwith ("Camlstack.stack_concat");
  memmove(Bp_val(s), Bp_val(s1), l1);
  memmove(&Byte(s, l1), Bp_val(s2), l2);
  return s;
}

/* [stack_caml_alloc_tuple s n m] allocates a tuple of [s] elements,
   where [n] of those elements will be initialized to pointers into
   the OCaml heap, as specified by the mask [m] (see stack_caml_alloc,
   above, for an explanation of the mask).
 */
value stack_caml_alloc_tuple (mlsize_t n, int nbits, int *mask)
{
  return stack_caml_alloc(n, 0, nbits, mask);
}

/***********************************************************************/
/* GC scanning */
/***********************************************************************/

/*
  scan_stack_roots is a routine called by the OCaml GC in order to
  scan the contents of the stack. This is enabled by setting this
  routine to the Caml runtime variable caml_scan_roots_hook, defined
  in file asmrun/roots.c (and byterun/roots.c), and initialized
  by the first call to stack_push_frame.

  scan_stack_roots works by iterating over the pointers marked by the
  allocation routines, as stored in the stack.c pointer mask. This is
  done by the stack.c routine [each_marked_pointer], which will invoke
  the function scanfun on each.

  scanfun scans each pointer it is given by invoking the provided
  scanning_action object [action], provided by the OCaml runtime.
*/

void (*prev_scan_roots_hook) (scanning_action a) = NULL;

static void scanfun(void *env, void **ptr) {
  scanning_action action = (scanning_action)env;
  value *root = (value *)ptr;
  value v = *root;
/*   printf("  scanning=%p, val=%p\n",root,(void *)v); */
/*   if (Is_long(v)) { */
/*     printf("   is long %d (%ld)\n", Int_val(v), Long_val(v)); */
/*   } else { */
/*     printf("   is block: Wosize=%lu, Tag=%u\n", Wosize_val(v), Tag_val(v)); */
/*   } */
  /* NOTE: We assume that the scanning action will ignore
     values v that are not blocks; caml_oldify_one seems to check,
     so I'll assume that non-block [v] values are safe. */
  action (v, root);
}

static void scan_stack_roots(scanning_action action)
{
  each_marked_pointer(scanfun,action);
  if (prev_scan_roots_hook != NULL) (*prev_scan_roots_hook)(action);
}

/***********************************************************************/
/* FFI */
/***********************************************************************/

/*
  These are the C implementations of the routines declared in camlstack.mli.
  Please see that file for descriptions of these routines.
 */

CAMLprim value stack_set_page_wosize(value lenv)
{
  int len = Int_val(lenv);
  set_page_szw(len) ;
  return Val_unit;
}

static int already_initialized = 0; /* tracks whether GC scanner initialized */

CAMLprim value stack_push_frame(value v)
{
#ifndef NOGC
  if (!already_initialized) {
    /* initializes the GC scanning hook if not yet initialized */
    already_initialized = 1;
    prev_scan_roots_hook = caml_scan_roots_hook;
    caml_scan_roots_hook = scan_stack_roots;
  }
#endif
  push_frame();
  return Val_unit;
}

CAMLprim value stack_pop_frame(value unit)
{
  pop_frame();
  return Val_unit;
}

CAMLprim value caml_is_stack_pointer(value v)
{
  int result = !Is_long(v) && is_stack_pointer((void *)v);
  return(Val_bool(result));
}

/* The next set of functions allocate immutable tuples.
   As such, they determine whether a field in the tuple
   may contain an OCaml pointer by examing the initializer.
   If the tuples were mutable, this would not be sufficient. */

CAMLprim value stack_mkpair(value v1, value v2)
{
  int mask[2];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 1;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 2;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(2,nbits,mask);
#ifdef DEBUG
  if (tuple == (value)0)
    caml_failwith ("Camlstack.mkpair");
  else
#endif
  {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    return(tuple);
  }
}

CAMLprim value stack_mktuple3(value v1, value v2, value v3) {
  int mask[3];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 1;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 2;
    nbits++;
  }
  if (!(Is_long(v3) || is_stack_pointer((void *)v3))) {
    mask[nbits] = 3;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(3,nbits,mask);
#ifdef DEBUG
  if (tuple == (value)0)
    caml_failwith ("Camlstack.mktuple3");
  else
#endif
  {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    Field(tuple, 2) = v3;
    return(tuple);
  }
}

CAMLprim value stack_mktuple4(value v1, value v2, value v3, value v4) {
  int mask[4];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 1;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 2;
    nbits++;
  }
  if (!(Is_long(v3) || is_stack_pointer((void *)v3))) {
    mask[nbits] = 3;
    nbits++;
  }
  if (!(Is_long(v4) || is_stack_pointer((void *)v4))) {
    mask[nbits] = 4;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(4,nbits,mask);
#ifdef DEBUG
  if (tuple == (value)0)
    caml_failwith ("Camlstack.mktuple4");
  else
#endif
  {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    Field(tuple, 2) = v3;
    Field(tuple, 3) = v4;
    return(tuple);
  }
}

CAMLprim value stack_mktuple5(value v1, value v2, value v3, value v4, value v5) {
  int mask[5];
  int nbits = 0;
  if (!(Is_long(v1) || is_stack_pointer((void *)v1))) {
    mask[0] = 1;
    nbits++;
  }
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[nbits] = 2;
    nbits++;
  }
  if (!(Is_long(v3) || is_stack_pointer((void *)v3))) {
    mask[nbits] = 3;
    nbits++;
  }
  if (!(Is_long(v4) || is_stack_pointer((void *)v4))) {
    mask[nbits] = 4;
    nbits++;
  }
  if (!(Is_long(v4) || is_stack_pointer((void *)v5))) {
    mask[nbits] = 5;
    nbits++;
  }
  value tuple = stack_caml_alloc_tuple(5,nbits,mask);
#ifdef DEBUG
  if (tuple == (value)0)
    caml_failwith ("Camlstack.mktuple4");
  else
#endif
  {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    Field(tuple, 2) = v3;
    Field(tuple, 3) = v4;
    Field(tuple, 4) = v5;
    return(tuple);
  }
}

CAMLprim value stack_mkref(value v)
{
  int mask[1] = { 1 }; /* Assume it could always be a pointer, since it could be mutated to one */
  value ref = stack_caml_alloc_tuple(1,1,mask);
#ifdef DEBUG
  if (ref == (value)0)
    caml_failwith ("Camlstack.mkref");
  else
#endif
  {
    Field(ref, 0) = v;
    return(ref);
  }
}

CAMLprim value stack_mkref_noscan(value v)
{
  value ref = stack_caml_alloc_tuple(1,0,NULL); /* Assume it will never contain a pointer */
#ifdef DEBUG
  if (ref == (value)0)
    caml_failwith ("Camlstack.mkref_noscan");
  else
#endif
  {
    Field(ref, 0) = v;
    return(ref);
  }
}

CAMLprim value stack_mkbytes(value lenv) {
  mlsize_t len = Int_val(lenv);
  if (len <= 0) {
    caml_invalid_argument ("Camlstack.mkbytes");
  }
  else {
    value str = stack_caml_alloc_string(len);
#ifdef DEBUG
    if (str == (value)0)
      caml_failwith ("Camlstack.mkbytes");
    else
#endif
      return(str);
  }
}

CAMLprim value stack_mkarray(value lenv, value initv) {
  int len = Int_val(lenv);
  if (len <= 0 || (Is_block(initv) && Tag_val(initv) == Double_tag))
    caml_invalid_argument ("Camlstack.mkarray");
  else {
    printf ("allocating array; len = %d\n", len);
    value tuple = stack_caml_alloc_tuple(len,-1,NULL); /* all possible heap pointers */
#ifdef DEBUG
    if (tuple == (value)0)
      caml_failwith ("Camlstack.mkarray");
    else
#endif
    {
      int i;
      for (i=0;i<len;i++) {
	Field(tuple, i) = initv;
      }
      return(tuple);
    }
  }
}

CAMLprim value stack_mkarray_noscan(value lenv, value initv) {
  int len = Int_val(lenv);
  if (len <= 0
      || (Is_block(initv)
	  && !(is_stack_pointer((void *)initv) || Tag_val(initv) == Double_tag)))
    caml_invalid_argument ("Camlstack.mkarray");
  else {
    int tag, n = len;
    if (Is_block(initv) && Tag_val(initv) == Double_tag) {
      tag = Double_array_tag;
      if (sizeof(value) == 4) n *= 2; /* if 32-bit words */
    } else tag = 0;
    value tuple = stack_caml_alloc(n,tag,0,NULL); /* no heap pointers */
#ifdef DEBUG
    if (tuple == (value)0)
      caml_failwith ("Camlstack.mkarray");
    else
#endif
    {
      int i;
      if (tag == Double_array_tag) {
	for (i=0;i<len;i++)
	  Store_double_field(tuple, i, Double_val(initv));
      }	else {
	for (i=0;i<len;i++)
	  Field(tuple, i) = initv;
      }
      return(tuple);
    }
  }
}

/** DEBUGGING **/

static int nptrs = 0;

void printptrs(void *ign, void **ptr) {
  printf("  live pointer addr=%p, val=%p\n",ptr,*ptr);
  nptrs++;
}

CAMLprim value print_mask(value unit)
{
  printf("identifying marked pointers\n");
  nptrs = 0;
  each_marked_pointer(printptrs,0);
  printf("%d pointers marked, in total\n", nptrs);
  return(Val_unit);
}

char *nextpad(char *pad) {
  if (strlen(pad) == 0) return "  ";
  if (strlen(pad) == 2) return "    ";
  if (strlen(pad) == 4) return "      ";
  return "        ";
}

void aux_inspect(value v, int level, char *pad) {
  if (Is_long(v)) {
    printf("%sis long %d (%ld)\n", pad, Int_val(v), Long_val(v));
  } else {
    int i;
    printf("%sis block: Wosize=%lu, Tag=%u\n", pad, Wosize_val(v), Tag_val(v));
    if (level == 0) return;
    if (Tag_val(v) == Double_array_tag) {
      return;
    } else if (Tag_val(v) == Custom_tag) {
      return;
    } else {
      for (i=0;i<Wosize_val(v); i++) {
	printf ("%sfield %d: ",pad, i);
	aux_inspect(Field(v,i),level-1,nextpad(pad));
      }
    }
  }
}

CAMLprim value inspect(value v)
{
  aux_inspect(v,2,"");
  return(Val_unit);
}
