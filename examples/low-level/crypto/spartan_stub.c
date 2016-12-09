#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#ifdef _WIN32
#define STDCALL __attribute__((stdcall))
#else
#define STDCALL
#endif

extern void STDCALL KeyExpansionStdcall(const void *key_ptr, void *expanded_key_ptr, void *placeholder);
extern void STDCALL AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr, void *placeholder);

void Spartan_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb)
{
  KeyExpansionStdcall(k, w, sb);
}

void Spartan_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb)
{
  AES128EncryptOneBlockStdcall(out, in, w, sb);
}
