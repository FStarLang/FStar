#include <stdint.h>
#include <stdio.h>
#include "fstarlib.h"

#define Bignum_Parameters_norm_length 5 
#define Bignum_Parameters_a24_prime 121665 
#define Bignum_Bigint_template int
#define Bignum_Bigint_template_const Bignum_Bigint_template
#define Bignum_Bigint_bigint uint64*
#define Bignum_Bigint_bigint_wide uint128_t*
#define Bignum_Bigint_bytes uint8*

typedef struct Curve_Point_point Curve_Point_point;
struct Curve_Point_point{
Bignum_Bigint_bigint x;
Bignum_Bigint_bigint y;
Bignum_Bigint_bigint z;
};


void decode_scalar(uint8 scalar[32]){
  scalar[0] &= 248;
  scalar[31] &= 127;
  scalar[31] |= 64;
}

void decode_input(uint64 x[5], uint8 sc[32]){
  uint64* s = (uint64*)sc;
  x[0] = s[0] & 0x7ffffffffffff;
  x[1] = ((s[0] >> 51) + (s[1] << 13)) & 0x7ffffffffffff;
  x[2] = ((s[1] >> 38) + (s[2] << 26)) & 0x7ffffffffffff;
  x[3] = ((s[2] >> 25) + (s[3] << 39)) & 0x7ffffffffffff;
  x[4] = (s[3] >> 12) & 0x7ffffffffffff;
}

void print_array(uint64* z, int len){
  int i;
  for (i=0; i < len; i++){
    printf("%lx ", z[i]);
  }
  printf("\n");
}

void print_long_array(uint128_t* z, int len){
  int i;
  for (i=0; i < len; i++){
    printf("%lx%lx ", (uint64)(z[i]>>64), (uint64)z[i]);
  }
  printf("\n");
}

void print_bigint(uint64 z[5]){
  uint64 x[4] = {0};
  int i, j;
  x[0] = z[0]       + (z[1] << 51);
  x[1] = (z[1] >> 13) + (z[2] << 38);
  x[2] = (z[2] >> 26) + (z[3] << 25);
  x[3] = (z[3] >> 39) + (z[4] << 12);
  for (i=0; i < 4; i++){
    for (j=0; j < 8; j++){
      printf("%lx ", 0xff & (x[i] >> (8*j)));
    }
    printf("\n");
  }
}

void test(){
  uint64 output[9], rx[9] = {0}, ry[9] = {0}, rz[9] = {0}, qx[9] = {0}, qy[9] = {0}, qz[9] = {1}, zrecip[9] = {0};
  uint64 axx[9] = {0}, ayy[9] = {0}, azz[9] = {0}, axxx[9] = {0}, ayyy[9] = {0}, azzz[9] = {0};
  uint8 scalar[32] = {0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d,
		      0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e, 0xdd,
		      0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18,
		      0x50, 0x6a, 0x22, 0x44, 0xba, 0x44, 0x9a, 0xc4};
  uint8 input[32] = {0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb,
		    0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f, 0x7c,
		    0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b,
		    0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab, 0x1c, 0x4c};
  char* expected = "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552";
  decode_scalar(scalar);
  decode_input(qx, input);

  Curve_Point_point basepoint = (Curve_Point_point) {qx, qy, qz};
  Curve_Point_point res = (Curve_Point_point) {rx, ry, rz};

  int i;
  printf(" Running 1000 computations of Curve25519 test vector ...\n");
  for (i=0;i<1000;i++){
    Curve_Ladder_montgomery_ladder(res, scalar, basepoint);
  }

  Bignum_Core_crecip_prime(zrecip, res.z);
  Bignum_Core_fmul(output, res.x, zrecip);
  
  printf("Expected:\n %s\nGot:\n", expected);
  print_bigint(output);
}

int main(int argc, char** argv){
  test();
  return 0;
}

