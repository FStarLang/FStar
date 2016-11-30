#include <stdint.h>

extern void __stdcall KeyExpansionStdcall(const void *key_ptr, void *expanded_key_ptr);
extern void __stdcall AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr);

void Spartan_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  KeyExpansionStdcall(k, w);
}

void Spartan_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  AES128EncryptOneBlockStdcall(out, in, w);
}

