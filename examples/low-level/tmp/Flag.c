#include "Flag.h"

bool Flag_cipher_prf(Crypto_Indexing_cipherAlg a)
{
  return false;
}

bool Flag_mac_log = false;

bool Flag_mac_int1cma(Crypto_Indexing_macAlg a)
{
  return false;
}

bool Flag_prf_cpa = false;

bool Flag_safeHS(Crypto_Indexing_id i)
{
  return false;
}

bool Flag_prf(Crypto_Indexing_id i)
{
  return false && false;
}

bool Flag_mac1(Crypto_Indexing_id i)
{
  return false && false;
}

bool Flag_safeId(Crypto_Indexing_id i)
{
  return false;
}

void Flag_mac1_implies_mac_log(Crypto_Indexing_id i)
{
  return;
}

void Flag_mac1_implies_prf(Crypto_Indexing_id i)
{
  return;
}

void Flag_safeId_implies_mac1(Crypto_Indexing_id i)
{
  return;
}

void Flag_safeId_implies_cpa(Crypto_Indexing_id i)
{
  return;
}

bool Flag_aes_ct = false;

