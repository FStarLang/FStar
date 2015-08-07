#include <caml/memory.h>
#include <caml/fail.h>
#include "camlstack.h"

CAMLprim value stack_mknode(value v1, value v2, value v3, value v4, value v5)
{
  CAMLparam5 (v1, v2, v3, v4, v5);
  int mask[4] = { 2, 3, 4, 6 };
  value tuple = stack_caml_alloc_tuple(6,4,mask);
  if (tuple == (value)0)
    caml_failwith ("Huffman.mknode");
  else {
    Field(tuple, 0) = Val_int(1);
    Field(tuple, 1) = v1;
    Field(tuple, 2) = v2;
    Field(tuple, 3) = v3;
    Field(tuple, 4) = v4;
    Field(tuple, 5) = v5;
    CAMLreturn(tuple);
  }
}
