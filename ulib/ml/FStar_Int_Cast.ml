(** Uints to Uints **)
type u8 = int
type u16 = int
type u32 = int
type u63 = int
type u64 = Stdint.Uint64.t
type u128 = Stdint.Uint128.t
type i8 = int
type i16 = int
type i32 = int
type i63 = int
type i64 = Int64.t

let uint8_to_uint64 (a:u8) : (u64) = Stdint.Uint64.of_int a
let uint8_to_uint63 (a:u8) : (u63) = a
let uint8_to_uint32 (a:u8) : (u32) = a
let uint8_to_uint16 (a:u8) : (u16) = a

let uint16_to_uint64 (a:u16) : (u64) = Stdint.Uint64.of_int a
let uint16_to_uint63 (a:u16) : (u63) = a
let uint16_to_uint32 (a:u16) : (u32) = a
let uint16_to_uint8  (a:u16) : (u8) = a land 255

let uint32_to_uint64 (a:u32) : (u64) = Stdint.Uint64.of_string (string_of_int a)
let uint32_to_uint63 (a:u32) : (u63) = a
let uint32_to_uint16 (a:u32) : (u16) = a land 65535
let uint32_to_uint8  (a:u32) : (u8) = a land 255

let uint63_to_uint64 (a:u63) : (u64) = Stdint.Uint64.of_string (string_of_int a)
let uint63_to_uint32 (a:u63) : (u32) = a land 4294967295
let uint63_to_uint16 (a:u63) : (u16) = a land 65535
let uint63_to_uint8  (a:u63) : (u8)  = a land 255

let uint64_to_uint63 (a:u64) : (u63) = Stdint.Uint64.to_int a
let uint64_to_uint32 (a:u64) : (u32) = Stdint.Uint64.to_int (Stdint.Uint64.logand a (Stdint.Uint64.of_int 4294967295))
let uint64_to_uint16 (a:u64) : (u16) = Stdint.Uint64.to_int (Stdint.Uint64.logand a (Stdint.Uint64.of_int 65535))     
let uint64_to_uint8  (a:u64) : (u8)  = int_of_string (Stdint.Uint64.to_string (Stdint.Uint64.logand a (Stdint.Uint64.of_string "255")))

  (* Stdint.Uint64.to_int (Stdint.Uint64.logand a (Stdint.Uint64.of_int 255)) *)

(** Ints to Ints **)
let int8_to_int64 (a:i8) : (i64) = Int64.of_int a
let int8_to_int63 (a:i8) : (i63) = a                                    
let int8_to_int32 (a:i8) : (i32) = a
let int8_to_int16 (a:i8) : (i16) = a

let int16_to_int64 (a:i16) : (i64) = Int64.of_int a
let int16_to_int63 (a:i16) : (i63) = a
let int16_to_int32 (a:i16) : (i32) = a
let int16_to_int8  (a:i16) : (i8 ) = a land 255

let int32_to_int64 (a:i32) : (i64) = Int64.of_int a                                                  
let int32_to_int63 (a:i32) : (i63) = a
let int32_to_int16 (a:i32) : (i16) = a land 65535
let int32_to_int8  (a:i32) : (i8 ) = a land 255

let int63_to_int64 (a:i63) : (i64) = Int64.of_int a                                                  
let int63_to_int32 (a:i63) : (i32) = a land 4294967295
let int63_to_int16 (a:i63) : (i16) = a land 65535
let int63_to_int8  (a:i63) : (i8 ) = a land 255

let int64_to_int63 (a:i64) : (i63) = Int64.to_int a
let int64_to_int32 (a:i64) : (i32) = (Int64.to_int a) land 4294967295
let int64_to_int16 (a:i64) : (i16) = (Int64.to_int a) land 65535
let int64_to_int8  (a:i64) : (i8 ) = (Int64.to_int a) land 255

(** Uints to Ints **)
let uint8_to_int64 (a:u8) : (i64) = Int64.of_int a
let uint8_to_int63 (a:u8) : (i63) = a
let uint8_to_int32 (a:u8) : (i32) = a
let uint8_to_int16 (a:u8) : (i16) = a
let uint8_to_int8  (a:u8) : (i8 ) = a

let uint16_to_int64 (a:u16) : (i64) = Int64.of_int a
let uint16_to_int63 (a:u16) : (i63) = a
let uint16_to_int32 (a:u16) : (i32) = a
let uint16_to_int16 (a:u16) : (i16) = a 
let uint16_to_int8  (a:u16) : (i8 ) = a land 255

let uint32_to_int64 (a:u32) : (i64) = Int64.of_int a
let uint32_to_int63 (a:u32) : (i63) = a
let uint32_to_int32 (a:u32) : (i32) = a 
let uint32_to_int16 (a:u32) : (i16) = a land 65535
let uint32_to_int8  (a:u32) : (i8 ) = a land 255

let uint63_to_int64 (a:u63) : (i64) = Int64.of_int a
let uint63_to_int63 (a:u63) : (i63) = a
let uint63_to_int32 (a:u63) : (i32) = a land 4294967295
let uint63_to_int16 (a:u63) : (i16) = a land 65535
let uint63_to_int8  (a:u63) : (i8 ) = a land 255

let uint64_to_int64 (a:u64) : (i64) = Stdint.Uint64.to_int64 a
let uint64_to_int63 (a:u64) : (i63) = Stdint.Uint64.to_int a
let uint64_to_int32 (a:u64) : (i32) = Stdint.Uint64.to_int a land 4294967295
let uint64_to_int16 (a:u64) : (i16) = Stdint.Uint64.to_int a land 65535                        
let uint64_to_int8  (a:u64) : (i8 ) = Stdint.Uint64.to_int a land 255

(** Ints to uints *)
let int8_to_uint64 (a:i8) : (u64) = Stdint.Uint64.of_int a
let int8_to_uint63 (a:i8) : (u63) = a
let int8_to_uint32 (a:i8) : (u32) = a
let int8_to_uint16 (a:i8) : (u16) = a
let int8_to_uint8  (a:i8) : (u8 ) = a

let int16_to_uint64 (a:i16) : (u64) = Stdint.Uint64.of_int a
let int16_to_uint63 (a:i16) : (u63) = a
let int16_to_uint32 (a:i16) : (u32) = a
let int16_to_uint16 (a:i16) : (u16) = a
let int16_to_uint8  (a:i16) : (u8 ) = a land 255

let int32_to_uint64 (a:i32) : (u64) = Stdint.Uint64.of_int a
let int32_to_uint63 (a:i32) : (u63) = a
let int32_to_uint32 (a:i32) : (u32) = a
let int32_to_uint16 (a:i32) : (u16) = a land 65535
let int32_to_uint8  (a:i32) : (u8 ) = a land 255

let int63_to_uint64 (a:i63) : (u64) = Stdint.Uint64.of_int a
let int63_to_uint63 (a:i63) : (u63) = a
let int63_to_uint32 (a:i63) : (u32) = a land 4294967295
let int63_to_uint16 (a:i63) : (u16) = a land 65535
let int63_to_uint8  (a:i63) : (u8 ) = a land 255

let int64_to_uint64 (a:i64) : (u64) = Stdint.Uint64.of_int64 a
let int64_to_uint63 (a:i64) : (u63) = Int64.to_int a
let int64_to_uint32 (a:i64) : (u32) = Int64.to_int a land 4294967295
let int64_to_uint16 (a:i64) : (u16) = Int64.to_int a land 65535                               
let  int64_to_uint8 (a:i64) : (u8 ) = Int64.to_int a land 255

let uint128_to_uint64 (a:u128) : (u64) = Stdint.Uint128.to_uint64 a
let uint64_to_uint128 (a:u64) : (u128) = Stdint.Uint64.to_uint128 a
