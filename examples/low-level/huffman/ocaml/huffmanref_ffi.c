#include <caml/memory.h>
#include <caml/fail.h>
#include "camlstack.h"
#include "stack.h"

extern value stack_mkref_noscan(value v); // in camlstack.c
extern value stack_mkref(value v);

static value empty_string = (value)0;

CAMLprim value stack_mknode(value v1, value v2, value v3, value v4, value v5)
{
  CAMLparam5 (v1, v2, v3, v4, v5);
  int mask[2];
  int nbits = 0;
  value v1ref, v2ref, v6ref;
  if (empty_string == (value)0)
    empty_string = stack_caml_alloc_string(1);
  v1ref = stack_mkref_noscan(v1);
  if (is_stack_pointer((void *)v2))
    v2ref = stack_mkref_noscan(v2);
  else
    v2ref = stack_mkref(v2);
  if (!(Is_long(v3) || is_stack_pointer((void *)v3))) {
    mask[nbits] = 3;
    nbits++;
  }
  if (!(Is_long(v4) || is_stack_pointer((void *)v4))) {
    mask[nbits] = 4;
    nbits++;
  }
  v6ref = stack_mkref_noscan(empty_string);
  value tuple = stack_caml_alloc_tuple(6,nbits,mask);
  if (tuple == (value)0)
    caml_failwith ("Huffman.mknode");
  else {
    Field(tuple, 0) = v1ref;
    Field(tuple, 1) = v2ref;
    Field(tuple, 2) = v3;
    Field(tuple, 3) = v4;
    Field(tuple, 4) = v5;
    Field(tuple, 5) = v6ref;
    CAMLreturn(tuple);
  }
}
