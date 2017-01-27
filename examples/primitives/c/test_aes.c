#include <stdint.h>
#include <stdio.h>
#include "fstarlib.h"


int main(){
  uint8 plaintext[16], key[32], ciphertext[16] = {0}, plaintext2[16] = {0};
  uint8 cipherkey[32] = {0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d, 0x77, 0x81 ,0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4};
  uint8 test[128] = {0}, w[240] = {0};
  int i;
  for (i = 0; i < 16; i++){
    plaintext[i] = i + (i << 4);
    key[2*i] = 2*i;
    key[2*i+1] = 2 * i + 1;
  }
  printf("Plaintext:\n");
  print_bytes(plaintext, 16);  
  printf("Key:\n");
  print_bytes(key, 32);
  printf("Expanded key:\n");
  Crypto_AES_keyExpansion(key, w);
  print_bytes(w, 240);

  Crypto_AES_cipher(ciphertext, plaintext, w);

  printf("Cipher text:\n");
  print_bytes(ciphertext, 16);

  printf("Decrypting cipher text:\n");  
  Crypto_AES_inv_cipher(plaintext2, ciphertext, w);
  print_bytes(plaintext2, 16);
  
  printf("\n");
  return 0;
}
