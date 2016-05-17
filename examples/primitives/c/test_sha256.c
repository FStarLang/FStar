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

void print_bytes2(char* bytes, int len){
  unsigned char i;
  for (i=0; i < len; i++){
    if (i < len - 1) printf("%02x:", bytes[i] & 0xff);
      else printf("%02x", bytes[i] & 0xff);
  }
  printf("\n");
}

int main(int argc, char** argv){
  uint8* msg = "abc";
  uint8* expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad";
  uint8 hash[32] = {0};

  printf("Running 1.000.000 iterations of sha256\n");
  unsigned int i;
  for(i = 0; i < 1000000; i++){
    sha256(hash, msg, 3);
  }

  sha256(hash, msg, 3);
  printf("%s\nGot: ", expected);
  print_bytes2(hash, 32);
  return 0;
}
