/* krml header omitted for test repeatability */


#include "Example_Slice.h"

typedef struct slice__uint8_t_s
{
  uint8_t *elt;
  size_t len;
}
slice__uint8_t;

static slice__uint8_t from_array__uint8_t(uint8_t *a, size_t alen)
{
  uint8_t *ptr = a;
  return ((slice__uint8_t){ .elt = ptr, .len = alen });
}

typedef struct __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t_s
{
  slice__uint8_t fst;
  slice__uint8_t snd;
}
__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t;

static __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
split__uint8_t(slice__uint8_t s, size_t i)
{
  uint8_t *elt_ = s.elt + i;
  slice__uint8_t s1 = { .elt = s.elt, .len = i };
  slice__uint8_t s2 = { .elt = elt_, .len = s.len - i };
  return
    ((__Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t){ .fst = s1, .snd = s2 });
}

static slice__uint8_t subslice__uint8_t(slice__uint8_t s, size_t i, size_t j)
{
  uint8_t *elt_ = s.elt + i;
  return ((slice__uint8_t){ .elt = elt_, .len = j - i });
}

static uint8_t op_Array_Access__uint8_t(slice__uint8_t a, size_t i)
{
  return a.elt[i];
}

static size_t len__uint8_t(slice__uint8_t s)
{
  return s.len;
}

static void op_Array_Assignment__uint8_t(slice__uint8_t a, size_t i, uint8_t v)
{
  a.elt[i] = v;
}

static void copy__uint8_t(slice__uint8_t dst, slice__uint8_t src)
{
  memcpy(dst.elt, src.elt, src.len * sizeof (uint8_t));
}

void Example_Slice_test(uint8_t *arr)
{
  slice__uint8_t slice = from_array__uint8_t(arr, (size_t)6U);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  s_ = split__uint8_t(slice, (size_t)2U);
  slice__uint8_t s1 = s_.fst;
  slice__uint8_t s2 = s_.snd;
  slice__uint8_t res = subslice__uint8_t(s2, (size_t)1U, (size_t)4U);
  slice__uint8_t s2_ = res;
  uint8_t x = op_Array_Access__uint8_t(s2_, len__uint8_t(s1));
  op_Array_Assignment__uint8_t(s1, (size_t)1U, x);
  __Pulse_Lib_Slice_slice__uint8_t_Pulse_Lib_Slice_slice__uint8_t
  s_1 = split__uint8_t(s2, (size_t)2U);
  slice__uint8_t s3 = s_1.fst;
  slice__uint8_t s4 = s_1.snd;
  copy__uint8_t(s3, s4);
}

