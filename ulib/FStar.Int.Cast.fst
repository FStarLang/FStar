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

let op_At_Percent = FStar.Int.op_At_Percent

/// Unsigned to unsigned

val uint8_to_uint64: a:U8.t -> Tot (b:U64.t{U64.v b = U8.v a})
let uint8_to_uint64 a = U64.uint_to_t (U8.v a)

val uint8_to_uint32: a:U8.t -> Tot (b:U32.t{U32.v b = U8.v a})
let uint8_to_uint32 x = U32.uint_to_t (U8.v x)

val uint8_to_uint16: a:U8.t -> Tot (b:U16.t{U16.v b = U8.v a})
let uint8_to_uint16 x = U16.uint_to_t (U8.v x)

val uint16_to_uint64: a:U16.t -> Tot (b:U64.t{U64.v b = U16.v a})
let uint16_to_uint64 x = U64.uint_to_t (U16.v x)

val uint16_to_uint32: a:U16.t -> Tot (b:U32.t{U32.v b = U16.v a})
let uint16_to_uint32 x = U32.uint_to_t (U16.v x)

val uint16_to_uint8 : a:U16.t -> Tot (b:U8.t{U8.v b = U16.v a % pow2 8})
let uint16_to_uint8 x = U8.uint_to_t (U16.v x % pow2 8)

val uint32_to_uint64: a:U32.t -> Tot (b:U64.t{U64.v b = U32.v a})
let uint32_to_uint64 x = U64.uint_to_t (U32.v x)

val uint32_to_uint16: a:U32.t -> Tot (b:U16.t{U16.v b = U32.v a % pow2 16})
let uint32_to_uint16 x = U16.uint_to_t (U32.v x % pow2 16)

val uint32_to_uint8 : a:U32.t -> Tot (b:U8.t{U8.v b = U32.v a % pow2 8})
let uint32_to_uint8 x = U8.uint_to_t (U32.v x % pow2 8)

val uint64_to_uint32: a:U64.t -> Tot (b:U32.t{U32.v b = U64.v a % pow2 32})
let uint64_to_uint32 x = U32.uint_to_t (U64.v x % pow2 32)

val uint64_to_uint16: a:U64.t -> Tot (b:U16.t{U16.v b = U64.v a % pow2 16})
let uint64_to_uint16 x = U16.uint_to_t (U64.v x % pow2 16)

val uint64_to_uint8 : a:U64.t -> Tot (b:U8.t{U8.v b = U64.v a % pow2 8})
let uint64_to_uint8 x = U8.uint_to_t (U64.v x % pow2 8)

/// Signed to signed

val int8_to_int64: a:I8.t -> Tot (b:I64.t{I64.v b = I8.v a})
let int8_to_int64 x = I64.int_to_t (I8.v x)

val int8_to_int32: a:I8.t -> Tot (b:I32.t{I32.v b = I8.v a})
let int8_to_int32 x = I32.int_to_t (I8.v x)

val int8_to_int16: a:I8.t -> Tot (b:I16.t{I16.v b = I8.v a})
let int8_to_int16 x = I16.int_to_t (I8.v x)

val int16_to_int64: a:I16.t -> Tot (b:I64.t{I64.v b = I16.v a})
let int16_to_int64 x = I64.int_to_t (I16.v x @% pow2 64)

val int16_to_int32: a:I16.t -> Tot (b:I32.t{I32.v b = I16.v a})
let int16_to_int32 x = I32.int_to_t (I16.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int16_to_int8 : a:I16.t -> Tot (b:I8.t {I8.v b  = (I16.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int16_to_int8 x = I8.int_to_t (I16.v x @% pow2 8)

val int32_to_int64: a:I32.t -> Tot (b:I64.t{I64.v b = I32.v a})
let int32_to_int64 x = I64.int_to_t (I32.v x @% pow2 64)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int32_to_int16: a:I32.t -> Tot (b:I16.t{I16.v b = (I32.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int32_to_int16 x = I16.int_to_t (I32.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int32_to_int8 : a:I32.t -> Tot (b:I8.t {I8.v b  = (I32.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int32_to_int8 x = I8.int_to_t (I32.v x @% pow2 8)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int64_to_int32: a:I64.t -> Tot (b:I32.t{I32.v b = (I64.v a @% pow2 32)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int32 x = I32.int_to_t (I64.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int64_to_int16: a:I64.t -> Tot (b:I16.t{I16.v b = (I64.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int16 x = I16.int_to_t (I64.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val int64_to_int8 : a:I64.t -> Tot (b:I8.t {I8.v b  = (I64.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let int64_to_int8 x = I8.int_to_t (I64.v x @% pow2 8)

/// Unsigned to signed

val uint8_to_int64: a:U8.t -> Tot (b:I64.t{I64.v b = U8.v a})
let uint8_to_int64 x = I64.int_to_t (U8.v x)

val uint8_to_int32: a:U8.t -> Tot (b:I32.t{I32.v b = U8.v a})
let uint8_to_int32 x = I32.int_to_t (U8.v x)

val uint8_to_int16: a:U8.t -> Tot (b:I16.t{I16.v b = U8.v a})
let uint8_to_int16 x = I16.int_to_t (U8.v x)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint8_to_int8 : a:U8.t -> Tot (b:I8.t {I8.v b  = (U8.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint8_to_int8 x = I8.int_to_t (U8.v x @% pow2 8)

val uint16_to_int64: a:U16.t -> Tot (b:I64.t{I64.v b = U16.v a})
let uint16_to_int64 x = I64.int_to_t (U16.v x)

val uint16_to_int32: a:U16.t -> Tot (b:I32.t{I32.v b = U16.v a})
let uint16_to_int32 x = I32.int_to_t (U16.v x)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint16_to_int16: a:U16.t -> Tot (b:I16.t{I16.v b = (U16.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint16_to_int16 x = I16.int_to_t (U16.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint16_to_int8 : a:U16.t -> Tot (b:I8.t {I8.v b  = (U16.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint16_to_int8 x = I8.int_to_t (U16.v x @% pow2 8)

val uint32_to_int64: a:U32.t -> Tot (b:I64.t{I64.v b = U32.v a})
let uint32_to_int64 x = I64.int_to_t (U32.v x)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint32_to_int32: a:U32.t -> Tot (b:I32.t{I32.v b = (U32.v a @% pow2 32)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int32 x = I32.int_to_t (U32.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint32_to_int16: a:U32.t -> Tot (b:I16.t{I16.v b = (U32.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int16 x = I16.int_to_t (U32.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint32_to_int8 : a:U32.t -> Tot (b:I8.t {I8.v b  = (U32.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint32_to_int8 x = I8.int_to_t (U32.v x @% pow2 8)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int64: a:U64.t -> Tot (b:I64.t{I64.v b = (U64.v a @% pow2 64)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int64 x = I64.int_to_t (U64.v x @% pow2 64)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int32: a:U64.t -> Tot (b:I32.t{I32.v b = (U64.v a @% pow2 32)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int32 x = I32.int_to_t (U64.v x @% pow2 32)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int16: a:U64.t -> Tot (b:I16.t{I16.v b = (U64.v a @% pow2 16)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int16 x = I16.int_to_t (U64.v x @% pow2 16)

[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
val uint64_to_int8 : a:U64.t -> Tot (b:I8.t {I8.v b  = (U64.v a @% pow2 8)})
[@@(deprecated "with care; in C the result is implementation-defined when not representable")]
let uint64_to_int8 x = I8.int_to_t (U64.v x @% pow2 8)

/// Signed to unsigned

val int8_to_uint64: a:I8.t -> Tot (b:U64.t{U64.v b = I8.v a % pow2 64})
let int8_to_uint64 x = U64.uint_to_t (I8.v x % pow2 64)

val int8_to_uint32: a:I8.t -> Tot (b:U32.t{U32.v b = I8.v a % pow2 32})
let int8_to_uint32 x = U32.uint_to_t (I8.v x % pow2 32)

val int8_to_uint16: a:I8.t -> Tot (b:U16.t{U16.v b = I8.v a % pow2 16})
let int8_to_uint16 x = U16.uint_to_t (I8.v x % pow2 16)

val int8_to_uint8 : a:I8.t -> Tot (b:U8.t {U8.v b  = I8.v a % pow2 8})
let int8_to_uint8 x = U8.uint_to_t (I8.v x % pow2 8)

val int16_to_uint64: a:I16.t -> Tot (b:U64.t{U64.v b = I16.v a % pow2 64})
let int16_to_uint64 x = U64.uint_to_t (I16.v x % pow2 64)

val int16_to_uint32: a:I16.t -> Tot (b:U32.t{U32.v b = I16.v a % pow2 32})
let int16_to_uint32 x = U32.uint_to_t (I16.v x % pow2 32)

val int16_to_uint16: a:I16.t -> Tot (b:U16.t{U16.v b = I16.v a % pow2 16})
let int16_to_uint16 x = U16.uint_to_t (I16.v x % pow2 16)

val int16_to_uint8 : a:I16.t -> Tot (b:U8.t {U8.v b  = I16.v a % pow2 8})
let int16_to_uint8 x = U8.uint_to_t (I16.v x % pow2 8)

val int32_to_uint64: a:I32.t -> Tot (b:U64.t{U64.v b = I32.v a % pow2 64})
let int32_to_uint64 x = U64.uint_to_t (I32.v x % pow2 64)

val int32_to_uint32: a:I32.t -> Tot (b:U32.t{U32.v b = I32.v a % pow2 32})
let int32_to_uint32 x = U32.uint_to_t (I32.v x % pow2 32)

val int32_to_uint16: a:I32.t -> Tot (b:U16.t{U16.v b = I32.v a % pow2 16})
let int32_to_uint16 x = U16.uint_to_t (I32.v x % pow2 16)

val int32_to_uint8 : a:I32.t -> Tot (b:U8.t {U8.v b  = I32.v a % pow2 8})
let int32_to_uint8 x = U8.uint_to_t (I32.v x % pow2 8)

val int64_to_uint64: a:I64.t -> Tot (b:U64.t{U64.v b = I64.v a % pow2 64})
let int64_to_uint64 x = U64.uint_to_t (I64.v x % pow2 64)

val int64_to_uint32: a:I64.t -> Tot (b:U32.t{U32.v b = I64.v a % pow2 32})
let int64_to_uint32 x = U32.uint_to_t (I64.v x % pow2 32)

val int64_to_uint16: a:I64.t -> Tot (b:U16.t{U16.v b = I64.v a % pow2 16})
let int64_to_uint16 x = U16.uint_to_t (I64.v x % pow2 16)

val int64_to_uint8 : a:I64.t -> Tot (b:U8.t {U8.v b  = I64.v a % pow2 8})
let int64_to_uint8 x = U8.uint_to_t (I64.v x % pow2 8)
