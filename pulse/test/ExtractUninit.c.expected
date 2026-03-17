/* krml header omitted for test repeatability */


#include "ExtractUninit.h"

uint32_t ExtractUninit_uninit_ref(void)
{
  uint32_t r;
  r = 3U;
  uint32_t __anf0 = r;
  return __anf0 + 29U;
}

uint32_t ExtractUninit_uninit_array(void)
{
  uint32_t arr[5U];
  arr[1U] = 2U;
  arr[3U] = 4U;
  uint32_t __anf1 = arr[1U];
  uint32_t __anf0 = arr[3U];
  return __anf1 + __anf0;
}

