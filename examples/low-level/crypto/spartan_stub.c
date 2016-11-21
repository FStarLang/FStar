#include <stdint.h>

extern __stdcall void keyExpansion(uint8_t *x0, uint8_t *x1, uint8_t *x2);
extern __stdcall void cipher(uint8_t *x0, uint8_t *x1, uint8_t *x2, uint8_t *x3);

void Spartan_keyExpansion(uint8_t *x0, uint8_t *x1, uint8_t *x2)
{
  keyExpansion(x0, x1, x2);
}

void Spartan_cipher(uint8_t *x0, uint8_t *x1, uint8_t *x2, uint8_t *x3)
{
  cipher(x0, x1, x2, x3);
}

