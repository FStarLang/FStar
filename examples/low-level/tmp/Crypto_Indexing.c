#include "Crypto_Indexing.h"

Crypto_Indexing_aeadAlg Crypto_Indexing_aeadAlg_of_id(Crypto_Indexing_id i)
{
  return i.cipher;
}

Crypto_Indexing_macAlg Crypto_Indexing_macAlg_of_id(Crypto_Indexing_id i)
{
  switch (i.cipher)
  {
    case Crypto_Indexing_aeadAlg_AES_128_GCM:
      {
        return Crypto_Indexing_macAlg_GHASH;
        break;
      }
    case Crypto_Indexing_aeadAlg_AES_256_GCM:
      {
        return Crypto_Indexing_macAlg_GHASH;
        break;
      }
    case Crypto_Indexing_aeadAlg_CHACHA20_POLY1305:
      {
        return Crypto_Indexing_macAlg_POLY1305;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

Crypto_Indexing_cipherAlg Crypto_Indexing_cipherAlg_of_id(Crypto_Indexing_id i)
{
  switch (i.cipher)
  {
    case Crypto_Indexing_aeadAlg_AES_128_GCM:
      {
        return Crypto_Indexing_cipherAlg_AES128;
        break;
      }
    case Crypto_Indexing_aeadAlg_AES_256_GCM:
      {
        return Crypto_Indexing_cipherAlg_AES256;
        break;
      }
    case Crypto_Indexing_aeadAlg_CHACHA20_POLY1305:
      {
        return Crypto_Indexing_cipherAlg_CHACHA20;
        break;
      }
    default:
      {
        printf("KreMLin incomplete match at %s:%d\n", __FILE__, __LINE__);
        exit(253);
      }
  }
}

Crypto_Indexing_id Crypto_Indexing_testId(Crypto_Indexing_aeadAlg a)
{
  return (Crypto_Indexing_id ){ .cipher = a, .uniq = (uint32_t )0 };
}

