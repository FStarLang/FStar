#include "Crypto_AEAD_Wrappers.h"

void
Crypto_AEAD_Wrappers_mac_wrapper(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
)
{
  Crypto_Symmetric_UF1CMA_mac(i, st, acc, tag);
  return;
}

bool
Crypto_AEAD_Wrappers_verify_wrapper(
  K___Crypto_Indexing_id_FStar_UInt128_t i,
  Crypto_Symmetric_UF1CMA_state____ st,
  Crypto_Symmetric_UF1CMA_accBuffer____ acc,
  uint8_t *tag
)
{
  bool b = Crypto_Symmetric_UF1CMA_verify(i, st, acc, tag);
  return b;
}

