#include <caml/memory.h>
#include <caml/fail.h>
#include "camlstack.h"

CAMLprim value stack_mkdt_B(value v) 
{
  CAMLparam1 (v);
  value tuple = stack_caml_alloc(1,0,0,NULL);
  if (tuple == (value)0)
    caml_failwith ("Camlstack.stack_mkdt_B");
  else {
    Field(tuple, 0) = v;
    CAMLreturn(tuple);
  }
}

CAMLprim value stack_mkdt_C(value v1, value v2) 
{
  CAMLparam2 (v1,v2);
  value tuple = stack_caml_alloc(2,1,0,NULL);
  if (tuple == (value)0)
    caml_failwith ("Camlstack.stack_mkdt_C");
  else {
    Field(tuple, 0) = v1;
    Field(tuple, 1) = v2;
    CAMLreturn(tuple);
  }
}

CAMLprim value stack_mkdt_D(value v) 
{
  CAMLparam1 (v);
  int mask[1] = { 1 };
  value tuple = stack_caml_alloc(1,2,1,mask);
  if (tuple == (value)0)
    caml_failwith ("Camlstack.stack_mkdt_D");
  else {
    Field(tuple, 0) = v;
    CAMLreturn(tuple);
  }
}
