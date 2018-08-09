#include <stdlib.h>

#include "connect.h"
#include "Hacl_SHA2_256.h"

void MerkleTree_Low_hash_from_hashes(uint8_t *src1, uint8_t *src2, uint8_t *dst)
{
  /* uint8_t *app = (uint8_t *) malloc(64); */
  uint8_t app[64];
  memcpy(app, src1, 32);
  memcpy(app + 32, src2, 32);

  Hacl_SHA2_256_hash(dst, src1, 64U);

  /* free(app); */
}
