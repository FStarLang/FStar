/* krml header omitted for test repeatability */


#include "InlineArrayLen.h"

int32_t InlineArrayLen_basic(void)
{
  int32_t arr[2U];
  for (uint32_t _i = 0U; _i < (size_t)2U; ++_i)
    arr[_i] = (int32_t)123;
  return arr[0U];
}

int32_t InlineArrayLen_use(void)
{
  int32_t arr[2U];
  for (uint32_t _i = 0U; _i < (size_t)2U; ++_i)
    arr[_i] = (int32_t)123;
  return arr[0U];
}

int32_t InlineArrayLen_use_gen_init(void)
{
  int32_t arr[2U];
  for (uint32_t _i = 0U; _i < (size_t)2U; ++_i)
    arr[_i] = (int32_t)123;
  return arr[0U];
}

int32_t InlineArrayLen_use_gen_init_st(void)
{
  int32_t __anf0 = (int32_t)123;
  int32_t arr[2U];
  for (uint32_t _i = 0U; _i < (size_t)2U; ++_i)
    arr[_i] = __anf0;
  return arr[0U];
}

int32_t InlineArrayLen_use_gen_len(void)
{
  int32_t arr[2U];
  for (uint32_t _i = 0U; _i < (size_t)2U; ++_i)
    arr[_i] = (int32_t)123;
  return arr[0U];
}

int32_t InlineArrayLen_use_gen_len_st(void)
{
  size_t __anf0 = (size_t)42U;
  KRML_CHECK_SIZE(sizeof (int32_t), __anf0);
  int32_t arr[__anf0];
  for (uint32_t _i = 0U; _i < __anf0; ++_i)
    arr[_i] = (int32_t)123;
  return arr[0U];
}

