
#include "fstarlib.h" 


// Rotate left and right for different sizes of integers
uint8 FStar_UInt8_op_Less_Less_Less(uint8 x, int y){
  return ((uint8)(x << y)) + (x >> (8 - y)); 
}

uint8 FStar_UInt8_op_Greater_Greater_Greater(uint8 x, int y){
  return (x >> y) + ((uint8)(x << (8 - y))); 
}

uint8 FStar_UInt8_rotate_left(uint8 x, int y){
  return ((uint8)(x << y)) + (x >> (8 - y)); 
}

uint8 FStar_UInt8_rotate_right(uint8 x, int y){
  return (x >> y) + ((uint8)(x << (8 - y))); 
}

inline uint32 FStar_UInt32_op_Less_Less_Less(uint32 x, int y){
  return ((uint32)(x << y)) + (x >> (32 - y)); 
}

inline uint32 FStar_UInt32_op_Greater_Greater_Greater(uint32 x, int y){
  return (x >> y) + ((uint32)(x << (32 - y))); 
}

uint64 FStar_UInt63_op_Less_Less_Less(uint64 x, int y){
  return ((uint64)(x << y)) + (x >> (64 - y)); 
}

uint64 FStar_UInt63_op_Greater_Greater_Greater(uint64 x, int y){
  return (x >> y) + ((uint64)(x << (64 - y))); 
}

uint64 FStar_UInt64_op_Less_Less_Less(uint64 x, int y){
  return ((uint64)(x << y)) + (x >> (64 - y)); 
}

uint64 FStar_UInt64_op_Greater_Greater_Greater(uint64 x, int y){
  return (x >> y) + ((uint64)(x << (64 - y))); 
}


// Converts bytes to and from int32s. Should be integrated to the compiler
void FStar_SBytes_sbytes_of_uint32s(uint8* res, uint32* b, int l){
  unsigned int i;
  uint32* tmp = (uint32*)res;
  for(i = 0; i < l; i++){
    tmp[i] = b[i];
  }
}

void FStar_SBytes_xor_bytes(uint8* output, uint8* a, uint8* b, int l){
  unsigned int i;
  for(i=0; i < l; i++){
    output[i] = a[i] ^ b[i];
  }
}

inline uint8 FStar_UInt8_gte(uint8 x, uint8 y){
  return (uint8)~(((int16_t)x) - y >> 15);
}

inline uint8 FStar_UInt8_eq(uint8 a, uint8 b){
  a = ~(a ^ b); 
  a &= a << 4;
  a &= a << 2;
  a &= a << 1;
  return ((char)a) >> 7;
}


// Constant time comparisons
uint32 FStar_UInt32_eq(uint32 a, uint32 b) {
  a = ~(a ^ b);
  a &= a << 16;
  a &= a << 8;
  a &= a << 4;
  a &= a << 2;
  a &= a << 1;
  return ((int32_t)a) >> 31;
}

uint32 FStar_UInt32_gte(uint32 a, uint32 b) {
  int64_t tmp;
  tmp = a - b;
  return ~(tmp >> 63);
}

uint64 FStar_UInt63_eq(uint64 a, uint64 b) {
  a = ~(a ^ b); 
  a &= a << 32;
  a &= a << 16;
  a &= a << 8;
  a &= a << 4;
  a &= a << 2;
  a &= a << 1;
  return ((int64_t)a) >> 63;
}

uint64 FStar_UInt63_gte(uint64 a, uint64 b) {
  a -= - b; // Works because a and b are never negative
  return ~(a >> 63);
}

uint64 FStar_UInt64_eq(uint64 a, uint64 b) {
  a = ~(a ^ b); 
  a &= a << 32;
  a &= a << 16;
  a &= a << 8;
  a &= a << 4;
  a &= a << 2;
  a &= a << 1;
  return ((int64_t)a) >> 63;
}

uint64 FStar_UInt64_gte(uint64 a, uint64 b) {
  return (uint64)~(((__int128_t)a) - b >> 127);
}

void print_bytes(uint8* b, int len){
  int i;
  for (i = 0; i < len; i++){
    if (b[i] < 0x10) {printf("0%x", 0xff & b[i]);}
    else {printf("%x", 0xff & b[i]);}
  }
  printf("\n");
}
