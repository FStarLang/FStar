#include "Buffer_Utils.h"

uint32_t Buffer_Utils_op_Greater_Greater_Greater(uint32_t a, uint32_t s)
{
  return a >> s | a << (uint32_t )32 - s;
}

uint32_t Buffer_Utils_op_Less_Less_Less(uint32_t a, uint32_t s)
{
  return a << s | a >> (uint32_t )32 - s;
}

void Buffer_Utils_xor_bytes_inplace(uint8_t *output, uint8_t *in1, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t i = len - (uint32_t )1;
    uint8_t in1i = in1[i];
    uint8_t oi = output[i];
    uint8_t oi0 = in1i ^ oi;
    output[i] = oi0;
    Buffer_Utils_xor_bytes_inplace(output, in1, i);
    return;
  }
}

void Buffer_Utils_lemma_euclidean_division(Prims_nat r, Prims_nat b, Prims_pos q)
{
  return;
}

void Buffer_Utils_lemma_uint32_of_bytes(uint32_t a, uint32_t b, uint32_t c, uint32_t d)
{
  return;
}

uint32_t Buffer_Utils_uint32_of_bytes(uint8_t *b)
{
  uint8_t b0 = b[(uint32_t )0];
  uint8_t b1 = b[(uint32_t )1];
  uint8_t b2 = b[(uint32_t )2];
  uint8_t b3 = b[(uint32_t )3];
  return
    (uint32_t )b0
    + ((uint32_t )b1 << (uint32_t )8)
    + ((uint32_t )b2 << (uint32_t )16)
    + ((uint32_t )b3 << (uint32_t )24);
}

void Buffer_Utils_bytes_of_uint32s(uint8_t *output, uint32_t *m, uint32_t l)
{
  if (l > (uint32_t )0)
  {
    uint32_t rem = l % (uint32_t )4;
    if (rem > (uint32_t )0)
    {
      uint32_t l0 = l - rem;
      uint32_t x = m[l0 / (uint32_t )4];
      uint8_t b0 = (uint8_t )(x & (uint32_t )255);
      output[l0] = b0;
      if (rem > (uint32_t )1)
      {
        uint8_t b1 = (uint8_t )(x >> (uint32_t )8 & (uint32_t )255);
        output[l0 + (uint32_t )1] = b1;
        if (rem > (uint32_t )2)
        {
          uint8_t b2 = (uint8_t )(x >> (uint32_t )16 & (uint32_t )255);
          output[l0 + (uint32_t )2] = b2;
        }
      }
      Buffer_Utils_bytes_of_uint32s(output, m, l0);
      return;
    }
    else
    {
      uint32_t l0 = l - (uint32_t )4;
      uint32_t x = m[l0 / (uint32_t )4];
      uint8_t b0 = (uint8_t )(x & (uint32_t )255);
      uint8_t b1 = (uint8_t )(x >> (uint32_t )8 & (uint32_t )255);
      uint8_t b2 = (uint8_t )(x >> (uint32_t )16 & (uint32_t )255);
      uint8_t b3 = (uint8_t )(x >> (uint32_t )24 & (uint32_t )255);
      output[l0] = b0;
      output[l0 + (uint32_t )1] = b1;
      output[l0 + (uint32_t )2] = b2;
      output[l0 + (uint32_t )3] = b3;
      Buffer_Utils_bytes_of_uint32s(output, m, l0);
      return;
    }
  }
  else
    return;
}

void Buffer_Utils_bytes_of_uint32(uint8_t *output, uint32_t x)
{
  uint8_t b0 = (uint8_t )x;
  uint8_t b1 = (uint8_t )(x >> (uint32_t )8);
  uint8_t b2 = (uint8_t )(x >> (uint32_t )16);
  uint8_t b3 = (uint8_t )(x >> (uint32_t )24);
  output[(uint32_t )0] = b0;
  output[(uint32_t )1] = b1;
  output[(uint32_t )2] = b2;
  output[(uint32_t )3] = b3;
}

void Buffer_Utils_memset(uint8_t *b, uint8_t z, uint32_t len)
{
  if (len == (uint32_t )0)
    return;
  else
  {
    uint32_t i = len - (uint32_t )1;
    Buffer_Utils_memset(b + (uint32_t )1, z, i);
    b[(uint32_t )0] = z;
  }
}

