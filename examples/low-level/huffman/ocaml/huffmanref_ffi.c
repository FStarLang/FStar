#include <caml/memory.h>
#include <caml/fail.h>
#include "camlstack.h"
#include "stack.h"

extern value stack_mkref_noscan(value v); // in camlstack.c
extern value stack_mkref(value v);

static value empty_string = (value)0;

CAMLprim value stack_mknode(value v1, value v2, value v3, value v4)
{
  CAMLparam4 (v1, v2, v3, v4);
  value v1ref, v5ref;
  if (empty_string == (value)0)
    empty_string = stack_caml_alloc_string(1);
  v1ref = stack_mkref_noscan(v1);
  /* assert (Is_long(v2) || is_stack_pointer((void *)v2)); */
  /* assert (Is_long(v3) || is_stack_pointer((void *)v3)); */
  v5ref = stack_mkref_noscan(empty_string);
  value tuple = stack_caml_alloc_tuple(5,0,NULL);
  if (tuple == (value)0)
    caml_failwith ("Huffman.mknode");
  else {
    Field(tuple, 0) = v1ref;
    Field(tuple, 1) = v2;
    Field(tuple, 2) = v3;
    Field(tuple, 3) = v4;
    Field(tuple, 4) = v5ref;
    CAMLreturn(tuple);
  }
}

CAMLprim value stack_mkpair_noscan(value v1, value v2) 
{
  CAMLparam2 (v1, v2);
  /* assert (Is_long(v1) || is_stack_pointer((void *)v1)); */
  /* assert (Is_long(v2) || is_stack_pointer((void *)v2)); */
  value tuple = stack_caml_alloc_tuple(2,0,NULL);
  if (tuple == (value)0)
    caml_failwith ("Camlstack.mkpair");
  else {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    CAMLreturn(tuple);
  }
}

CAMLprim value stack_mktriple_noscan(value v1, value v2, value v3) 
{
  CAMLparam3 (v1, v2, v3);
  /* assert (Is_long(v1) || is_stack_pointer((void *)v1)); */
  /* assert (Is_long(v2) || is_stack_pointer((void *)v2)); */
  /* assert (Is_long(v3) || is_stack_pointer((void *)v3)); */
  value tuple = stack_caml_alloc_tuple(3,0,NULL);
  if (tuple == (value)0)
    caml_failwith ("Camlstack.mktriple_noscan");
  else {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    Field(tuple, 2) = v3;
    CAMLreturn(tuple);
  }
}
