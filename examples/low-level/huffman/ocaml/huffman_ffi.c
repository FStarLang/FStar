#include <caml/memory.h>
#include <caml/fail.h>
#include "camlstack.h"
#include "stack.h"

static value empty_string = (value)0;

CAMLprim value stack_mknode(value v1, value v2, value v3, value v4, value v5)
{
  CAMLparam5 (v1, v2, v3, v4, v5);
  int mask[3];
  int nbits = 0;
  if (empty_string == (value)0)
    empty_string = stack_caml_alloc_string(1);
  if (!(Is_long(v2) || is_stack_pointer((void *)v2))) {
    mask[0] = 2;
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
  value tuple = stack_caml_alloc_tuple(6,nbits,mask);
  if (tuple == (value)0)
    caml_failwith ("Huffman.mknode");
  else {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    Field(tuple, 2) = v3;
    Field(tuple, 3) = v4;
    Field(tuple, 4) = v5;
    Field(tuple, 5) = empty_string;
    CAMLreturn(tuple);
  }
}
