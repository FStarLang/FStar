#include "FStar_BitVector.h"

void *FStar_BitVector_zero_vec(Prims_pos n)
{
  return FStar_Seq_create(n, false);
}

void *FStar_BitVector_elem_vec(Prims_pos n, Prims_nat i)
{
  return FStar_Seq_upd(FStar_Seq_create(n, false), i, true);
}

void *FStar_BitVector_ones_vec(Prims_pos n)
{
  return FStar_Seq_create(n, true);
}

void *FStar_BitVector_logand_vec(Prims_pos n, void *a, void *b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *FStar_BitVector_logxor_vec(Prims_pos n, void *a, void *b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *FStar_BitVector_logor_vec(Prims_pos n, void *a, void *b)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *FStar_BitVector_lognot_vec(Prims_pos n, void *a)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void FStar_BitVector_logand_vec_definition(Prims_pos n, void *a, void *b, Prims_nat i)
{
  return;
}

void FStar_BitVector_logxor_vec_definition(Prims_pos n, void *a, void *b, Prims_nat i)
{
  return;
}

void FStar_BitVector_logor_vec_definition(Prims_pos n, void *a, void *b, Prims_nat i)
{
  return;
}

void FStar_BitVector_lognot_vec_definition(Prims_pos n, void *a, Prims_nat i)
{
  return;
}

void FStar_BitVector_lemma_xor_bounded(Prims_pos m, Prims_nat n, void *x, void *y)
{
  return;
}

void *FStar_BitVector_shift_left_vec(Prims_pos n, void *a, Prims_nat s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void *FStar_BitVector_shift_right_vec(Prims_pos n, void *a, Prims_nat s)
{
  printf("KreMLin abort at %s:%d\n", __FILE__, __LINE__);
  exit(255);
}

void FStar_BitVector_shift_left_vec_lemma_1(Prims_pos n, void *a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_BitVector_shift_left_vec_lemma_2(Prims_pos n, void *a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_BitVector_shift_right_vec_lemma_1(Prims_pos n, void *a, Prims_nat s, Prims_nat i)
{
  return;
}

void FStar_BitVector_shift_right_vec_lemma_2(Prims_pos n, void *a, Prims_nat s, Prims_nat i)
{
  return;
}

