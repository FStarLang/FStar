#include "FStar_UInt.h"

Prims_int FStar_UInt_max_int(Prims_nat n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_min_int(Prims_nat n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

bool FStar_UInt_fits(Prims_int x, Prims_nat n)
{
  return
    Prims_op_LessThanOrEqual(FStar_UInt_min_int(n),
      x)
    && Prims_op_LessThanOrEqual(x, FStar_UInt_max_int(n));
}

Prims_int FStar_UInt_zero(Prims_nat n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_pow2_n(Prims_pos n, Prims_nat p)
{
  return Prims_pow2(p);
}

Prims_int FStar_UInt_one(Prims_pos n)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_ones(Prims_nat n)
{
  return FStar_UInt_max_int(n);
}

Prims_int FStar_UInt_incr(Prims_nat n, Prims_int a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_decr(Prims_nat n, Prims_int a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_incr_underspec(Prims_nat n, Prims_int a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_decr_underspec(Prims_nat n, Prims_int a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_incr_mod(Prims_nat n, Prims_int a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_decr_mod(Prims_nat n, Prims_int a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_add(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Addition(a, b);
}

Prims_int FStar_UInt_add_underspec(Prims_nat n, Prims_int a, Prims_int b)
{
  if (FStar_UInt_fits(Prims_op_Addition(a, b), n))
    return Prims_op_Addition(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_UInt_add_mod(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Modulus(Prims_op_Addition(a, b), Prims_pow2(n));
}

Prims_int FStar_UInt_sub(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Subtraction(a, b);
}

Prims_int FStar_UInt_sub_underspec(Prims_nat n, Prims_int a, Prims_int b)
{
  if (FStar_UInt_fits(Prims_op_Subtraction(a, b), n))
    return Prims_op_Subtraction(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_UInt_sub_mod(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Modulus(Prims_op_Subtraction(a, b), Prims_pow2(n));
}

Prims_int FStar_UInt_mul(Prims_nat n, Prims_int a, Prims_int b)
{
  return FStar_Mul_op_Star(a, b);
}

Prims_int FStar_UInt_mul_underspec(Prims_nat n, Prims_int a, Prims_int b)
{
  if (FStar_UInt_fits(FStar_Mul_op_Star(a, b), n))
    return FStar_Mul_op_Star(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_UInt_mul_mod(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Modulus(FStar_Mul_op_Star(a, b), Prims_pow2(n));
}

Prims_int FStar_UInt_div(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Division(a, b);
}

Prims_int FStar_UInt_div_underspec(Prims_nat n, Prims_int a, Prims_int b)
{
  if (FStar_UInt_fits(Prims_op_Division(a, b), n))
    return Prims_op_Division(a, b);
  else
    return Prims_magic((uint8_t )0);
}

Prims_int FStar_UInt_mod_(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_Subtraction(a, FStar_Mul_op_Star(Prims_op_Division(a, b), b));
}

bool FStar_UInt_eq(Prims_nat n, Prims_int a, Prims_int b)
{
  return a == b;
}

bool FStar_UInt_gt(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_GreaterThan(a, b);
}

bool FStar_UInt_gte(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_GreaterThanOrEqual(a, b);
}

bool FStar_UInt_lt(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_LessThan(a, b);
}

bool FStar_UInt_lte(Prims_nat n, Prims_int a, Prims_int b)
{
  return Prims_op_LessThanOrEqual(a, b);
}

Prims_int FStar_UInt_to_uint_t(Prims_nat m, Prims_int a)
{
  return Prims_op_Modulus(a, Prims_pow2(m));
}

void *FStar_UInt_to_vec(Prims_nat n, Prims_int num)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

Prims_int FStar_UInt_from_vec(Prims_nat n, void *vec)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void FStar_UInt_to_vec_lemma_1(Prims_nat n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_to_vec_lemma_2(Prims_nat n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_inverse_aux(Prims_nat n, void *vec, Prims_nat i)
{
  return;
}

void FStar_UInt_inverse_vec_lemma(Prims_nat n, void *vec)
{
  return;
}

void FStar_UInt_inverse_num_lemma(Prims_nat n, Prims_int num)
{
  return;
}

void FStar_UInt_from_vec_lemma_1(Prims_nat n, void *a, void *b)
{
  return;
}

void FStar_UInt_from_vec_lemma_2(Prims_nat n, void *a, void *b)
{
  return;
}

void FStar_UInt_from_vec_aux(Prims_nat n, void *a, Prims_nat s1, Prims_nat s2)
{
  return;
}

void
FStar_UInt_seq_slice_lemma(
  Prims_nat n,
  void *a,
  Prims_nat s1,
  Prims_nat t1,
  Prims_nat s2,
  Prims_nat t2
)
{
  return;
}

void FStar_UInt_from_vec_propriety(Prims_pos n, void *a, Prims_nat s)
{
  return;
}

void FStar_UInt_append_lemma(Prims_pos n, Prims_pos m, void *a, void *b)
{
  return;
}

void FStar_UInt_slice_left_lemma(Prims_pos n, void *a, Prims_pos s)
{
  return;
}

void FStar_UInt_slice_right_lemma(Prims_pos n, void *a, Prims_pos s)
{
  return;
}

void FStar_UInt_zero_to_vec_lemma(Prims_pos n, Prims_nat i)
{
  return;
}

void FStar_UInt_zero_from_vec_lemma(Prims_pos n)
{
  return;
}

void FStar_UInt_one_to_vec_lemma(Prims_pos n, Prims_nat i)
{
  return;
}

void FStar_UInt_pow2_to_vec_lemma(Prims_pos n, Prims_nat p, Prims_nat i)
{
  return;
}

void FStar_UInt_pow2_from_vec_lemma(Prims_pos n, Prims_nat p)
{
  return;
}

void FStar_UInt_ones_to_vec_lemma(Prims_pos n, Prims_nat i)
{
  return;
}

void FStar_UInt_ones_from_vec_lemma(Prims_pos n)
{
  return;
}

bool FStar_UInt_nth(Prims_pos n, Prims_int a, Prims_nat i)
{
  return FStar_Seq_index(FStar_UInt_to_vec(n, a), i);
}

void FStar_UInt_nth_lemma(Prims_pos n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_zero_nth_lemma(Prims_pos n, Prims_nat i)
{
  return;
}

void FStar_UInt_pow2_nth_lemma(Prims_pos n, Prims_nat p, Prims_nat i)
{
  return;
}

void FStar_UInt_one_nth_lemma(Prims_pos n, Prims_nat i)
{
  return;
}

void FStar_UInt_ones_nth_lemma(Prims_pos n, Prims_nat i)
{
  return;
}

Prims_int FStar_UInt_logand(Prims_pos n, Prims_int a, Prims_int b)
{
  return
    FStar_UInt_from_vec(n,
      FStar_BitVector_logand_vec(n, FStar_UInt_to_vec(n, a), FStar_UInt_to_vec(n, b)));
}

Prims_int FStar_UInt_logxor(Prims_pos n, Prims_int a, Prims_int b)
{
  return
    FStar_UInt_from_vec(n,
      FStar_BitVector_logxor_vec(n, FStar_UInt_to_vec(n, a), FStar_UInt_to_vec(n, b)));
}

Prims_int FStar_UInt_logor(Prims_pos n, Prims_int a, Prims_int b)
{
  return
    FStar_UInt_from_vec(n,
      FStar_BitVector_logor_vec(n, FStar_UInt_to_vec(n, a), FStar_UInt_to_vec(n, b)));
}

Prims_int FStar_UInt_lognot(Prims_pos n, Prims_int a)
{
  return FStar_UInt_from_vec(n, FStar_BitVector_lognot_vec(n, FStar_UInt_to_vec(n, a)));
}

void FStar_UInt_logand_definition(Prims_pos n, Prims_int a, Prims_int b, Prims_nat i)
{
  return;
}

void FStar_UInt_logxor_definition(Prims_pos n, Prims_int a, Prims_int b, Prims_nat i)
{
  return;
}

void FStar_UInt_logor_definition(Prims_pos n, Prims_int a, Prims_int b, Prims_nat i)
{
  return;
}

void FStar_UInt_lognot_definition(Prims_pos n, Prims_int a, Prims_nat i)
{
  return;
}

void FStar_UInt_logand_commutative(Prims_pos n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_logand_associative(Prims_pos n, Prims_int a, Prims_int b, Prims_int c)
{
  return;
}

void FStar_UInt_logand_self(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logand_lemma_1(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logand_lemma_2(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logxor_commutative(Prims_pos n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_logxor_associative(Prims_pos n, Prims_int a, Prims_int b, Prims_int c)
{
  return;
}

void FStar_UInt_logxor_self(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logxor_lemma_1(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logxor_lemma_2(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logxor_inv(Prims_pos n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_logor_commutative(Prims_pos n, Prims_int a, Prims_int b)
{
  return;
}

void FStar_UInt_logor_associative(Prims_pos n, Prims_int a, Prims_int b, Prims_int c)
{
  return;
}

void FStar_UInt_logor_self(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logor_lemma_1(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_logor_lemma_2(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_lognot_self(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_lognot_lemma_1(Prims_pos n)
{
  return;
}

void FStar_UInt_logor_disjoint(Prims_pos n, Prims_int a, Prims_int b, Prims_pos m)
{
  return;
}

void FStar_UInt_logand_mask(Prims_pos n, Prims_int a, Prims_pos m)
{
  return;
}

Prims_int FStar_UInt_shift_left(Prims_pos n, Prims_int a, Prims_nat s)
{
  return FStar_UInt_from_vec(n, FStar_BitVector_shift_left_vec(n, FStar_UInt_to_vec(n, a), s));
}

Prims_int FStar_UInt_shift_right(Prims_pos n, Prims_int a, Prims_nat s)
{
  return FStar_UInt_from_vec(n, FStar_BitVector_shift_right_vec(n, FStar_UInt_to_vec(n, a), s));
}

void FStar_UInt_shift_left_lemma_1(Prims_pos n, Prims_int a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_UInt_shift_left_lemma_2(Prims_pos n, Prims_int a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_UInt_shift_right_lemma_1(Prims_pos n, Prims_int a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_UInt_shift_right_lemma_2(Prims_pos n, Prims_int a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_UInt_shift_left_logand_lemma(Prims_pos n, Prims_int a, Prims_int b, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_right_logand_lemma(Prims_pos n, Prims_int a, Prims_int b, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_left_logxor_lemma(Prims_pos n, Prims_int a, Prims_int b, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_right_logxor_lemma(Prims_pos n, Prims_int a, Prims_int b, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_left_logor_lemma(Prims_pos n, Prims_int a, Prims_int b, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_right_logor_lemma(Prims_pos n, Prims_int a, Prims_int b, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_left_value_aux_1(Prims_pos n, Prims_int a, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_left_value_aux_2(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_shift_left_value_aux_3(Prims_pos n, Prims_int a, Prims_pos s)
{
  return;
}

void FStar_UInt_shift_left_value_lemma(Prims_pos n, Prims_int a, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_right_value_aux_1(Prims_pos n, Prims_int a, Prims_nat s)
{
  return;
}

void FStar_UInt_shift_right_value_aux_2(Prims_pos n, Prims_int a)
{
  return;
}

void FStar_UInt_shift_right_value_aux_3(Prims_pos n, Prims_int a, Prims_pos s)
{
  return;
}

void FStar_UInt_shift_right_value_lemma(Prims_pos n, Prims_int a, Prims_nat s)
{
  return;
}

