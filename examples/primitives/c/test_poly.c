#include <stdint.h>
#include <stdio.h>
#include "fstarlib.h"

#define Parameters_platform_size 63 
#define Parameters_platform_wide 63 
#define Parameters_norm_length 5 
#define Parameters_bytes_length 17 
#define Parameters_ndiff_prime 26 
#define Parameters_ndiff 28 

void print_array(uint64* array, int len){
  unsigned char i;
  for (i=0; i < len; i++){
    printf("%lx ", array[i]);
  }
  printf("\n");
}

void print_bytes(char* bytes, int len){
  unsigned char i;
  for (i=0; i < len; i++){
    printf("%x ", bytes[i] & 0xff);
  }
  printf("\n");
}

int main(int argc, char** argv){
  uint8 key[32] = {0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33, 
		   0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8, 
		   0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd, 
		   0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b};
  uint8* msg = "Cryptographic Forum Research Group";
  uint8* expected = "Tag: a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9";
  uint8 hash[16] = {0};

  /*
  uint64 a[9] = {2}, b[9] = {3}, c[9] = {10}, tmp[9] = {0};
  Bignum_fsum_prime (a, b);
  print_array(a, 5);
  Bignum_multiplication(tmp,a, c); 
  print_array(tmp, 9);

  Bignum_freduce_degree (tmp)  ; 
  print_array(tmp, 9);
  b [ Parameters_norm_length ] =  FStar_UInt63_zero;
  print_array(tmp, 9);
  Bignum_carry (tmp, 0); 
  print_array(tmp, 9);
  Bignum_carry2 (tmp); 
  print_array(tmp, 9);
  Bignum_last_carry (tmp);

  print_array(tmp, 5);
    Poly_add_and_multiply(a, b, c);
  */

  //  print_bytes(key, 16);
  //uint64 acc[9] = {0}, r[5] = {0};
  //Poly_clamp(key);
  //Poly_le_bytes_to_num(r, key);

  //Poly_poly1305_step(msg, acc, r, 2);
  
  //Poly_num_to_le_bytes(hash, acc);

  printf("Running 1.000.000 iterations of poly1305's test vector from RFC\n");
  unsigned int i;
  for(i = 0; i < 1000000; i++){
    Poly_poly1305_mac(hash, msg, 34, key);    
  }

  Poly_poly1305_mac(hash, msg, 34, key);
  printf("%s\nGot; ", expected);
  print_bytes(hash, 16);
  return 0;
}
