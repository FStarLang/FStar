#include "FStar_Int.h"

void FStar_Int_pow2_values(Prims_nat x)
{
  return;
}

Prims_int FStar_Int_op_Slash(Prims_int a, Prims_int b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_Int_div_eucl(Prims_int a, Prims_nonzero b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_Int_op_Slash_Percent(Prims_int x0, Prims_nonzero x1)
{
  return FStar_Int_div_eucl(x0, x1);
}

Prims_int FStar_Int_op_At_Percent(Prims_int v, Prims_int p)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_Int_max_int(Prims_pos n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_Int_min_int(Prims_pos n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

bool FStar_Int_fits(Prims_int x, Prims_pos n)
{
  return
    Prims_op_LessThanOrEqual(FStar_Int_min_int(n),
      x)
    && Prims_op_LessThanOrEqual(x, FStar_Int_max_int(n));
}

Prims_int FStar_Int_add(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_Addition(a, b);
}

Prims_int FStar_Int_add_underspec(Prims_pos n, Prims_int a, Prims_int b)
{
  if (FStar_Int_fits(Prims_op_Addition(a, b), n))
    return Prims_op_Addition(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_Int_add_mod(Prims_pos n, Prims_int a, Prims_int b)
{
  return FStar_Int_op_At_Percent(Prims_op_Addition(a, b), Prims_pow2(n));
}

Prims_int FStar_Int_sub(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_Subtraction(a, b);
}

Prims_int FStar_Int_sub_underspec(Prims_pos n, Prims_int a, Prims_int b)
{
  if (FStar_Int_fits(Prims_op_Subtraction(a, b), n))
    return Prims_op_Subtraction(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_Int_sub_mod(Prims_pos n, Prims_int a, Prims_int b)
{
  return FStar_Int_op_At_Percent(Prims_op_Subtraction(a, b), Prims_pow2(n));
}

Prims_int FStar_Int_mul(Prims_pos n, Prims_int a, Prims_int b)
{
  return FStar_Mul_op_Star(a, b);
}

Prims_int FStar_Int_mul_underspec(Prims_pos n, Prims_int a, Prims_int b)
{
  if (FStar_Int_fits(FStar_Mul_op_Star(a, b), n))
    return FStar_Mul_op_Star(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_Int_mul_mod(Prims_pos n, Prims_int a, Prims_int b)
{
  return FStar_Int_op_At_Percent(FStar_Mul_op_Star(a, b), Prims_pow2(n));
}

Prims_int FStar_Int_div(Prims_pos n, Prims_int a, Prims_int b)
{
  return FStar_Int_op_Slash(a, b);
}

Prims_int FStar_Int_div_underspec(Prims_pos n, Prims_int a, Prims_int b)
{
  if (FStar_Int_fits(FStar_Int_op_Slash(a, b), n))
    return FStar_Int_op_Slash(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_Int_mod_(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_Subtraction(a, FStar_Mul_op_Star(FStar_Int_op_Slash(a, b), b));
}

bool FStar_Int_eq(Prims_pos n, Prims_int a, Prims_int b)
{
  return a == b;
}

bool FStar_Int_gt(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_GreaterThan(a, b);
}

bool FStar_Int_gte(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_GreaterThanOrEqual(a, b);
}

bool FStar_Int_lt(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_LessThan(a, b);
}

bool FStar_Int_lte(Prims_pos n, Prims_int a, Prims_int b)
{
  return Prims_op_LessThanOrEqual(a, b);
}

Prims_int FStar_Int_to_int_t(Prims_pos m, Prims_int a)
{
  return FStar_Int_op_At_Percent(a, Prims_pow2(m));
}

Prims_int FStar_Int_shift_left(Prims_pos n, Prims_int a, Prims_nat s)
{
  return FStar_Int_op_At_Percent(FStar_Mul_op_Star(a, Prims_pow2(s)), Prims_pow2(n));
}

