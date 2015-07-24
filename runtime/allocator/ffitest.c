#include <stdio.h>
#include <string.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include "stack.h"


#define check(_p) if (!(_p)) { fprintf(stderr,"Failed check %s:%d\n",__FILE__,__LINE__); fflush(stdout); exit(1); }
#define Assert check

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

/***********************************************************************/
/* Allocating OCaml values on the stack */
/***********************************************************************/

value stack_caml_alloc(mlsize_t wosize, tag_t tag, int nbits, int *mask) {
  value tmp, result;
  mlsize_t i;
  Assert (tag < 256);
  Assert (tag != Infix_tag);
  Assert (wosize != 0);
  /*NOTE: for the below call to make sense, the mask that was passed
    in should index words starting at 1, so as to skip over the header
    word. */
  tmp = (value)stack_alloc_maskp(Bhsize_wosize(wosize),nbits,mask);
  Assert (tmp != 0);
  Hd_hp (tmp) = Make_header (wosize, tag, Caml_black);
  result = Val_hp (tmp);
  if (tag < No_scan_tag){
    for (i = 0; i < wosize; i++) Field (result, i) = Val_unit;
  }
  return result;
}

value stack_caml_alloc_string (mlsize_t lenb)
{
  value result;
  mlsize_t offset_index;
  mlsize_t wosize = (lenb + sizeof (value)) / sizeof (value);
  result = stack_caml_alloc (wosize, String_tag, 0, NULL);
  Field (result, wosize - 1) = 0;
  offset_index = Bsize_wsize (wosize) - 1;
  Byte (result, offset_index) = offset_index - lenb;
  return result;
}

value stack_caml_alloc_tuple (mlsize_t n, int nbits, int *mask)
{
  return stack_caml_alloc(n, 0, nbits, mask);
}

/***********************************************************************/
/* GC scanning */
/***********************************************************************/

void (*prev_scan_roots_hook) (scanning_action a) = NULL;

static void scanfun(void *env, void **ptr) {
  scanning_action action = (scanning_action)env;
  value *root = (value *)ptr;
  value v = *root;
#ifndef NDEBUG
  printf("  scanning=%p, val=%p\n",root,(void *)v);
  if (Is_long(v)) {
    printf("   is long %d (%ld)\n", Int_val(v), Long_val(v));
  } else {
    printf("   is block: Wosize=%lu, Tag=%hhu\n", Wosize_val(v), Tag_val(v));
  }
#endif
  action (v, root);
}

static void scan_stack_roots(scanning_action action)
{
  each_marked_pointer(scanfun,action);
  /* Run the previous hook if any */
  if (prev_scan_roots_hook != NULL) (*prev_scan_roots_hook)(action);
}

/***********************************************************************/
/* FFI */
/***********************************************************************/

CAMLprim value stack_push_frame(value v) 
{
  int szb = Val_int(v);
  static int already_initialized = 0;
  if (!already_initialized) {
    already_initialized = 1;
    prev_scan_roots_hook = caml_scan_roots_hook;
    caml_scan_roots_hook = scan_stack_roots;
  }
  push_frame(szb);
  return Val_unit;
}

CAMLprim value stack_pop_frame() 
{
  pop_frame();
  return Val_unit;
}

CAMLprim value stack_mkpair(value v1, value v2) 
{
  CAMLparam2 (v1, v2);
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
  Field(tuple, 0) = v1;
  Field(tuple, 1) = v2;
  CAMLreturn(tuple);
}

CAMLprim value stack_mktuple3(value v1, value v2, value v3) {
  CAMLparam3 (v1, v2, v3);
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
  Field(tuple, 0) = v1;
  Field(tuple, 1) = v2;
  Field(tuple, 2) = v3;
  CAMLreturn(tuple);
}

CAMLprim value stack_mktuple4(value v1, value v2, value v3, value v4) {
  CAMLparam4 (v1, v2, v3, v4);
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
  Field(tuple, 0) = v1;
  Field(tuple, 1) = v2;
  Field(tuple, 2) = v3;
  Field(tuple, 3) = v4;
  CAMLreturn(tuple);
}

CAMLprim value stack_mkemptystring(value vallen) {
  CAMLparam1 (vallen);
  int len = Int_val(vallen);
  CAMLreturn(stack_caml_alloc_string(len));
}

/***********************************************************************/
/* Tests */
/***********************************************************************/

static char *s = "This is a string!";
CAMLprim value make_string(value unit)
{
  int len;
  value res;

  len = strlen(s);
  res = stack_caml_alloc_string(len);
  memmove(String_val(res), s, len);
  return res;
}

void printptrs(void *ign, void **ptr) {
  printf("  live pointer addr=%p, val=%p\n",ptr,*ptr);
}

CAMLprim void print_mask(value unit) 
{
  CAMLparam1 (unit);
  printf("identifying marked pointers\n");
  each_marked_pointer(printptrs,0);
  CAMLreturn0;
}

CAMLprim void inspect(value v) 
{
  CAMLparam1 (v);
  if (Is_long(v)) {
    printf("is long %d (%ld)\n", Int_val(v), Long_val(v));
  } else {
    printf("is block: Wosize=%lu, Tag=%hhu\n", Wosize_val(v), Tag_val(v));
  }
  CAMLreturn0;
}
