/* @flow */

export type u8 = number;
export type u16 = number;
export type u32 = number;
export type u63 = number;
export type u64 = number;
export type u128 = number;
export type i8 = number;
export type i16 = number;
export type i32 = number;
export type i63 = number;
export type i64 = number;

export let uint8_to_uint64 = (a:u8) : (u64) => a;
export let uint8_to_uint63 = (a:u8) : (u63) => a;
export let uint8_to_uint32 = (a:u8) : (u32) => a;
export let uint8_to_uint16 = (a:u8) : (u16) => a;

export let uint16_to_uint64 = (a:u16) : (u64) => a;
export let uint16_to_uint63 = (a:u16) : (u63) => a;
export let uint16_to_uint32 = (a:u16) : (u32) => a;
export let uint16_to_uint8  = (a:u16) : (u8) => a & 255;

export let uint32_to_uint64 = (a:u32) : (u64) => a;
export let uint32_to_uint63 = (a:u32) : (u63) => a;
export let uint32_to_uint16 = (a:u32) : (u16) => a & 65535;
export let uint32_to_uint8  = (a:u32) : (u8) => a & 255;

export let uint63_to_uint64 = (a:u63) : (u64) => a;
export let uint63_to_uint32 = (a:u63) : (u32) => a & 4294967295;
export let uint63_to_uint16 = (a:u63) : (u16) => a & 65535;
export let uint63_to_uint8  = (a:u63) : (u8)  => a & 255;

export let uint64_to_uint63 = (a:u64) : (u63) => a;
export let uint64_to_uint32 = (a:u64) : (u32) => a & 4294967295;
export let uint64_to_uint16 = (a:u64) : (u16) => a & 65535;     
export let uint64_to_uint8  = (a:u64) : (u8)  => a & 255;

/* Ints to Ints */ 
export let int8_to_int64 = (a:i8) : (i64) => a;
export let int8_to_int63 = (a:i8) : (i63) => a;                                    
export let int8_to_int32 = (a:i8) : (i32) => a;
export let int8_to_int16 = (a:i8) : (i16) => a;

export let int16_to_int64 = (a:i16) : (i64) => a;
export let int16_to_int63 = (a:i16) : (i63) => a;
export let int16_to_int32 = (a:i16) : (i32) => a;
export let int16_to_int8  = (a:i16) : (i8 ) => a & 255;

export let int32_to_int64 = (a:i32) : (i64) => a;                                                  
export let int32_to_int63 = (a:i32) : (i63) => a;
export let int32_to_int16 = (a:i32) : (i16) => a & 65535;
export let int32_to_int8  = (a:i32) : (i8 ) => a & 255;

export let int63_to_int64 = (a:i63) : (i64) => a;
export let int63_to_int32 = (a:i63) : (i32) => a & 4294967295;
export let int63_to_int16 = (a:i63) : (i16) => a & 65535;
export let int63_to_int8  = (a:i63) : (i8 ) => a & 255;

export let int64_to_int63 = (a:i64) : (i63) => a;
export let int64_to_int32 = (a:i64) : (i32) => a & 4294967295;
export let int64_to_int16 = (a:i64) : (i16) => a & 65535;
export let int64_to_int8  = (a:i64) : (i8 ) => a & 255;

/* Uints to Ints */
export let uint8_to_int64 = (a:u8) : (i64) => a;
export let uint8_to_int63 = (a:u8) : (i63) => a;
export let uint8_to_int32 = (a:u8) : (i32) => a;
export let uint8_to_int16 = (a:u8) : (i16) => a;
export let uint8_to_int8  = (a:u8) : (i8 ) => a;

export let uint16_to_int64 = (a:u16) : (i64) => a;
export let uint16_to_int63 = (a:u16) : (i63) => a;
export let uint16_to_int32 = (a:u16) : (i32) => a;
export let uint16_to_int16 = (a:u16) : (i16) => a; 
export let uint16_to_int8  = (a:u16) : (i8 ) => a & 255;

export let uint32_to_int64 = (a:u32) : (i64) => a;
export let uint32_to_int63 = (a:u32) : (i63) => a;
export let uint32_to_int32 = (a:u32) : (i32) => a; 
export let uint32_to_int16 = (a:u32) : (i16) => a & 65535;
export let uint32_to_int8  = (a:u32) : (i8 ) => a & 255;

export let uint63_to_int64 = (a:u63) : (i64) => a;
export let uint63_to_int63 = (a:u63) : (i63) => a;
export let uint63_to_int32 = (a:u63) : (i32) => a & 4294967295;
export let uint63_to_int16 = (a:u63) : (i16) => a & 65535;
export let uint63_to_int8  = (a:u63) : (i8 ) => a & 255;

export let uint64_to_int64 = (a:u64) : (i64) => a;
export let uint64_to_int63 = (a:u64) : (i63) => a;
export let uint64_to_int32 = (a:u64) : (i32) => a & 4294967295;
export let uint64_to_int16 = (a:u64) : (i16) => a & 65535;                        
export let uint64_to_int8  = (a:u64) : (i8 ) => a & 255;

/* Ints to uints */
export let int8_to_uint64 = (a:i8) : (u64) => a;
export let int8_to_uint63 = (a:i8) : (u63) => a;
export let int8_to_uint32 = (a:i8) : (u32) => a;
export let int8_to_uint16 = (a:i8) : (u16) => a;
export let int8_to_uint8  = (a:i8) : (u8 ) => a;

export let int16_to_uint64 = (a:i16) : (u64) => a;
export let int16_to_uint63 = (a:i16) : (u63) => a;
export let int16_to_uint32 = (a:i16) : (u32) => a;
export let int16_to_uint16 = (a:i16) : (u16) => a;
export let int16_to_uint8  = (a:i16) : (u8 ) => a & 255;

export let int32_to_uint64 = (a:i32) : (u64) => a;
export let int32_to_uint63 = (a:i32) : (u63) => a;
export let int32_to_uint32 = (a:i32) : (u32) => a;
export let int32_to_uint16 = (a:i32) : (u16) => a & 65535;
export let int32_to_uint8  = (a:i32) : (u8 ) => a & 255;

export let int63_to_uint64 = (a:i63) : (u64) => a;
export let int63_to_uint63 = (a:i63) : (u63) => a;
export let int63_to_uint32 = (a:i63) : (u32) => a & 4294967295;
export let int63_to_uint16 = (a:i63) : (u16) => a & 65535;
export let int63_to_uint8  = (a:i63) : (u8 ) => a & 255;

export let int64_to_uint64 = (a:i64) : (u64) => a;
export let int64_to_uint63 = (a:i64) : (u63) => a;
export let int64_to_uint32 = (a:i64) : (u32) => a & 4294967295;
export let int64_to_uint16 = (a:i64) : (u16) => a & 65535;                               
export let  int64_to_uint8 = (a:i64) : (u8 ) => a & 255;

export let uint128_to_uint64 = (a:u128) : (u64) => a;
export let uint64_to_uint128 = (a:u64) : (u128) => a;