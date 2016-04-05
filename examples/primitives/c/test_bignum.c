#include <stdint.h>
#include <stdio.h>
#include "fstarlib.h"

#define LEN 5

void print_array(uint64* array){
  unsigned char i;
  for (i=0; i < LEN; i++){
    printf("%ld ", array[i]);
  }
  printf("\n");
}

void print_long_array(uint128* array){
  unsigned char i;
  for (i=0; i < 2*LEN-1; i++){
    printf("%ld|%ld ", (uint64)(array[i] >> 64), (uint64)array[i]);
  }
  printf("\n");
}

void test_sum(){
  uint64 a[5] = {0, 1, 2, 3, 4}, b[5] = {1, 2, 3, 4, 5};  
  Bignum_Core_fsum(a,b);
  print_array(a);
  return;
}

void test_difference(){
  uint64 a[5] = {0, 1, 2, 3, 4}, b[5] = {4, 4, 4, 4, 4};  
  Bignum_Core_fdifference(a,b);
  print_array(a);
  return;
}

void test_mul(){
  uint128 c[9] = {0};
  uint64 a[5] = {0, 1, 2, 3, 4}, b[5] = {4, 4, 4, 4, 4}, d[5] = {0};  
  Bignum_Fproduct_multiplication(c,a,b);
  print_long_array(c);
  Bignum_Core_fmul(d,a,b);
  print_array(d);
  return;
}

int main(int argc, char** argv){
  test_sum();
  test_difference();
  test_mul();
  return 0;
}
