
#include <stdint.h>
#include <string.h>
#include <stdio.h>

// Integer constants
#define FStar_UInt64_one_wide ((uint128_t)1)
#define FStar_UInt64_zero_wide ((uint128_t)0)
#define FStar_UInt64_one ((uint64)1)
#define FStar_UInt64_zero ((uint64)0)
#define FStar_UInt63_one ((uint64)1)
#define FStar_UInt63_zero ((uint64)0)
#define FStar_UInt32_one ((uint32)1)
#define FStar_UInt32_zero ((uint32)0)
#define FStar_UInt8_one ((uint8)1)
#define FStar_UInt8_zero ((uint8)0)

// Native FStar types (necessary while lemmas are not erased)
typedef int FStar_Heap_heap;
typedef unsigned uint128_t __attribute__((mode(TI)));

#undef force_inline
#define force_inline __attribute__((always_inline))

typedef uint128_t uint128;
typedef uint64_t uint64;
typedef uint64_t uint63;
typedef uint32_t uint32;
typedef uint8_t uint8;

// Bignum types
typedef uint64_t* Bigint_bigint;
typedef uint8* Bignum_Bigint_bytes;
typedef uint64_t* Bignum_Bigint_bigint;
typedef uint128_t* Bignum_Bigint_bigint_wide;

// Rotate left and right for different sizes of integers
uint8 FStar_UInt8_op_Less_Less_Less(uint8 x, int y);
uint8 FStar_UInt8_op_Greater_Greater_Greater(uint8 x, int y);
uint8 FStar_UInt8_rotate_left(uint8 x, int y);
uint8 FStar_UInt8_rotate_right(uint8 x, int y);
uint32 FStar_UInt32_op_Less_Less_Less(uint32 x, int y);
uint32 FStar_UInt32_op_Greater_Greater_Greater(uint32 x, int y);
uint64 FStar_UInt63_op_Less_Less_Less(uint64 x, int y);
uint64 FStar_UInt63_op_Greater_Greater_Greater(uint64 x, int y);
uint64 FStar_UInt64_op_Less_Less_Less(uint64 x, int y);
uint64 FStar_UInt64_op_Greater_Greater_Greater(uint64 x, int y);

void FStar_SBytes_sbytes_of_uint32s(uint8* res, uint32* b, int l);
void FStar_SBytes_xor_bytes(uint8* output, uint8* a, uint8* b, int l);

// Constant time comparisons
uint32 FStar_UInt32_eq(uint32 a, uint32 b);
uint32 FStar_UInt32_gte(uint32 a, uint32 b);
uint64 FStar_UInt63_eq(uint64 a, uint64 b);
uint64 FStar_UInt63_gte(uint64 a, uint64 b);
uint64 FStar_UInt64_eq(uint64 a, uint64 b);
uint64 FStar_UInt64_gte(uint64 a, uint64 b);

// Debugging functions
void print_bytes(uint8* b, int len);

