/* krml header omitted for test repeatability */


#include "Break.h"

void Break_simple_break(void)
{
  bool k = true;
  bool _break = false;
  while (!_break && k)
    _break = true;
}

void Break_break_continue_and_return(uint8_t which)
{
  bool _return = false;
  uint32_t i = 0U;
  bool _break = false;
  bool cond;
  if (_break)
    cond = false;
  else if (_return)
    cond = false;
  else
  {
    uint32_t __anf0 = i;
    cond = __anf0 < 1000U;
  }
  while (cond)
  {
    bool _continue = false;
    if (which == 0U)
      _break = true;
    if (!_break)
    {
      if (which == 1U)
        _continue = true;
      if (!_continue)
      {
        if (which == 2U)
          _return = true;
        if (!_return)
        {
          uint32_t __anf0 = i;
          i = __anf0 + 1U;
        }
      }
    }
    bool ite;
    if (_break)
      ite = false;
    else if (_return)
      ite = false;
    else
    {
      uint32_t __anf0 = i;
      ite = __anf0 < 1000U;
    }
    cond = ite;
  }
}

size_t Break_find_zero_with_break(int32_t *a, size_t sz)
{
  size_t i = (size_t)0U;
  bool _break = false;
  bool cond;
  if (_break)
    cond = false;
  else
  {
    size_t __anf0 = i;
    cond = __anf0 < sz;
  }
  while (cond)
  {
    size_t __anf01 = i;
    int32_t __anf1 = a[__anf01];
    if (__anf1 == 0)
      _break = true;
    if (!_break)
    {
      size_t __anf02 = i;
      i = __anf02 + (size_t)1U;
    }
    bool ite;
    if (_break)
      ite = false;
    else
    {
      size_t __anf0 = i;
      ite = __anf0 < sz;
    }
    cond = ite;
  }
  return i;
}

