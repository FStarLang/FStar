#include <stdlib.h>

#include "connect.h"
#include "Hacl_SHA2_256.h"

int is_hash_zero(uint8_t *h)
{
  uint8_t sum = 0;
  for (int i = 0; i < 32; ++i) {
    sum |= h[i];
  }

  if (sum == 0) return 1;

  return 0;
}

void MerkleTree_Low_hash_from_hashes(uint8_t *src1, uint8_t *src2, uint8_t *dst)
{

  if (is_hash_zero(src1)) {
    memcpy(dst, src2, 32);
    return;
  }

  if (is_hash_zero(src2)) {
    memcpy(dst, src1, 32);
    return;
  }
  
  uint8_t *app = (uint8_t *) malloc(64);
  memcpy(app, src1, 32);
  memcpy(app + 32, src2, 32);

  Hacl_SHA2_256_hash(dst, src1, 64U);

  free(app);
}
