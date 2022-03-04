(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Int.Cast

module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

/// Unsigned to unsigned

let uint8_to_uint64 x = U64.uint_to_t (U8.v x)

let uint8_to_uint32 x = U32.uint_to_t (U8.v x)

let uint8_to_uint16 x = U16.uint_to_t (U8.v x)

let uint16_to_uint64 x = U64.uint_to_t (U16.v x)

let uint16_to_uint32 x = U32.uint_to_t (U16.v x)

let uint16_to_uint8 x = U8.uint_to_t (U16.v x % pow2 8)

let uint32_to_uint64 x = U64.uint_to_t (U32.v x)

let uint32_to_uint16 x = U16.uint_to_t (U32.v x % pow2 16)

let uint32_to_uint8 x = U8.uint_to_t (U32.v x % pow2 8)

let uint64_to_uint32 x = U32.uint_to_t (U64.v x % pow2 32)

let uint64_to_uint16 x = U16.uint_to_t (U64.v x % pow2 16)

let uint64_to_uint8 x = U8.uint_to_t (U64.v x % pow2 8)

/// Signed to signed

let int8_to_int64 x = I64.int_to_t (I8.v x)

let int8_to_int32 x = I32.int_to_t (I8.v x)

let int8_to_int16 x = I16.int_to_t (I8.v x)

let int16_to_int64 x = I64.int_to_t (I16.v x @% pow2 64)

let int16_to_int32 x = I32.int_to_t (I16.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int16_to_int8 x = I8.int_to_t (I16.v x @% pow2 8)

let int32_to_int64 x = I64.int_to_t (I32.v x @% pow2 64)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int32_to_int16 x = I16.int_to_t (I32.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int32_to_int8 x = I8.int_to_t (I32.v x @% pow2 8)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int32 x = I32.int_to_t (I64.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int16 x = I16.int_to_t (I64.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int8 x = I8.int_to_t (I64.v x @% pow2 8)

/// Unsigned to signed

let uint8_to_int64 x = I64.int_to_t (U8.v x)

let uint8_to_int32 x = I32.int_to_t (U8.v x)

let uint8_to_int16 x = I16.int_to_t (U8.v x)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint8_to_int8 x = I8.int_to_t (U8.v x @% pow2 8)

let uint16_to_int64 x = I64.int_to_t (U16.v x)

let uint16_to_int32 x = I32.int_to_t (U16.v x)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint16_to_int16 x = I16.int_to_t (U16.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint16_to_int8 x = I8.int_to_t (U16.v x @% pow2 8)

let uint32_to_int64 x = I64.int_to_t (U32.v x)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int32 x = I32.int_to_t (U32.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int16 x = I16.int_to_t (U32.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int8 x = I8.int_to_t (U32.v x @% pow2 8)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int64 x = I64.int_to_t (U64.v x @% pow2 64)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int32 x = I32.int_to_t (U64.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int16 x = I16.int_to_t (U64.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int8 x = I8.int_to_t (U64.v x @% pow2 8)

/// Signed to unsigned

let int8_to_uint64 x = U64.uint_to_t (I8.v x % pow2 64)

let int8_to_uint32 x = U32.uint_to_t (I8.v x % pow2 32)

let int8_to_uint16 x = U16.uint_to_t (I8.v x % pow2 16)

let int8_to_uint8 x = U8.uint_to_t (I8.v x % pow2 8)

let int16_to_uint64 x = U64.uint_to_t (I16.v x % pow2 64)

let int16_to_uint32 x = U32.uint_to_t (I16.v x % pow2 32)

let int16_to_uint16 x = U16.uint_to_t (I16.v x % pow2 16)

let int16_to_uint8 x = U8.uint_to_t (I16.v x % pow2 8)

let int32_to_uint64 x = U64.uint_to_t (I32.v x % pow2 64)

let int32_to_uint32 x = U32.uint_to_t (I32.v x % pow2 32)

let int32_to_uint16 x = U16.uint_to_t (I32.v x % pow2 16)

let int32_to_uint8 x = U8.uint_to_t (I32.v x % pow2 8)

let int64_to_uint64 x = U64.uint_to_t (I64.v x % pow2 64)

let int64_to_uint32 x = U32.uint_to_t (I64.v x % pow2 32)

let int64_to_uint16 x = U16.uint_to_t (I64.v x % pow2 16)

let int64_to_uint8 x = U8.uint_to_t (I64.v x % pow2 8)
