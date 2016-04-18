module FStar.Int.Cast

module U8  = FStar.UInt.UInt8
module U16 = FStar.UInt.UInt16
module U32 = FStar.UInt.UInt32
module U63 = FStar.UInt.UInt63
module U64 = FStar.UInt.UInt64
module I8  = FStar.Int.Int8
module I16 = FStar.Int.Int16
module I32 = FStar.Int.Int32
module I63 = FStar.Int.Int63
module I64 = FStar.Int.Int64

type u8  = U8.uint8
type u16 = U16.uint16
type u32 = U32.uint32
type u63 = U63.uint63
type u64 = U64.uint64

type i8  = I8.int8
type i16 = I16.int16
type i32 = I32.int32
type i63 = I63.int63
type i64 = I64.int64

let op_At_Percent = FStar.Int.op_At_Percent

(** Uints to Uints **)
assume val uint8_to_uint64: a:u8 -> Tot (b:u64{U64.v b = U8.v a})
assume val uint8_to_uint63: a:u8 -> Tot (b:u63{U63.v b = U8.v a})
assume val uint8_to_uint32: a:u8 -> Tot (b:u32{U32.v b = U8.v a})
assume val uint8_to_uint16: a:u8 -> Tot (b:u16{U16.v b = U8.v a})

assume val uint16_to_uint64: a:u16 -> Tot (b:u64{U64.v b = U16.v a})
assume val uint16_to_uint63: a:u16 -> Tot (b:u63{U63.v b = U16.v a})
assume val uint16_to_uint32: a:u16 -> Tot (b:u32{U32.v b = U16.v a})
//assume val uint16_to_uint8: a:u16 -> Tot (b:u8{b = U8.int_to_uint8 (U16.v a)})
assume val uint16_to_uint8 : a:u16 -> Tot (b:u8{U8.v b = U16.v a % FStar.UInt.pow2 8})

assume val uint32_to_uint64: a:u32 -> Tot (b:u64{U64.v b = U32.v a})
assume val uint32_to_uint63: a:u32 -> Tot (b:u63{U63.v b = U32.v a})
//assume val uint32_to_uint16: a:u32 -> Tot (b:u16{b = U16.int_to_uint16 (U32.v a)})
//assume val uint32_to_uint8: a:u32 -> Tot (b:u8{b = U8.int_to_uint8 (U32.v a)})
assume val uint32_to_uint16: a:u32 -> Tot (b:u16{U16.v b = U32.v a % FStar.UInt.pow2 16})
assume val uint32_to_uint8 : a:u32 -> Tot (b:u8{U8.v b = U32.v a % FStar.UInt.pow2 8})

assume val uint63_to_uint64: a:u63 -> Tot (b:u64{U64.v b = U63.v a})
//assume val uint63_to_uint32: a:u63 -> Tot (b:u32{b = U32.int_to_uint32 (U63.v a)})
//assume val uint63_to_uint16: a:u63 -> Tot (b:u16{b = U16.int_to_uint16 (U63.v a)})
//assume val uint63_to_uint8: a:u63 -> Tot (b:u8{b = U8.int_to_uint8 (U63.v a)})
assume val uint63_to_uint32: a:u63 -> Tot (b:u32{U32.v b = U63.v a % FStar.UInt.pow2 32})
assume val uint63_to_uint16: a:u63 -> Tot (b:u16{U16.v b = U63.v a % FStar.UInt.pow2 16})
assume val uint63_to_uint8 : a:u63 -> Tot (b:u8{U8.v b = U63.v a % FStar.UInt.pow2 8})

//assume val uint64_to_uint63: a:u64 -> Tot (b:u63{U63.v b = U63.int_to_uint63 (U64.v a)})
//assume val uint64_to_uint32: a:u64 -> Tot (b:u32{U32.v b = U32.int_to_uint32 (U64.v a})
//assume val uint64_to_uint16: a:u64 -> Tot (b:u16{U16.v b = U16.int_to_uint16 (U64.v a})
//assume val uint64_to_uint8: a:u64 -> Tot (b:u8{U8.v b = U8.int_to_uint8 (U64.v a})
assume val uint64_to_uint63: a:u64 -> Tot (b:u63{U63.v b = U64.v a % FStar.UInt.pow2 63})
assume val uint64_to_uint32: a:u64 -> Tot (b:u32{U32.v b = U64.v a % FStar.UInt.pow2 32})
assume val uint64_to_uint16: a:u64 -> Tot (b:u16{U16.v b = U64.v a % FStar.UInt.pow2 16})
assume val uint64_to_uint8 : a:u64 -> Tot (b:u8{U8.v b = U64.v a % FStar.UInt.pow2 8})

(** Ints to Ints **)
assume val int8_to_int64: a:i8 -> Tot (b:i64{I64.v b = I8.v a})
assume val int8_to_int63: a:i8 -> Tot (b:i63{I63.v b = I8.v a})
assume val int8_to_int32: a:i8 -> Tot (b:i32{I32.v b = I8.v a})
assume val int8_to_int16: a:i8 -> Tot (b:i16{I16.v b = I8.v a})

assume val int16_to_int64: a:i16 -> Tot (b:i64{I64.v b = I16.v a})
assume val int16_to_int63: a:i16 -> Tot (b:i63{I63.v b = I16.v a})
assume val int16_to_int32: a:i16 -> Tot (b:i32{I32.v b = I16.v a})
//assume val int16_to_int8: a:i16 -> Tot (b:u8{b = I8.int_to_int8 (I16.v a)})
assume val int16_to_int8 : a:i16 -> Tot (b:i8 {I8.v b  = (I16.v a @% FStar.Int.pow2 8)})

assume val int32_to_int64: a:i32 -> Tot (b:i64{I64.v b = I32.v a})
assume val int32_to_int63: a:i32 -> Tot (b:i63{I63.v b = I32.v a})
//assume val int32_to_int16: a:i32 -> Tot (b:i16{b = I16.int_to_int16 (I32.v a)})
//assume val int32_to_int8: a:i32 -> Tot (b:i8{b = I8.int_to_int8 (I32.v a)})
assume val int32_to_int16: a:i32 -> Tot (b:i16{I16.v b = (I32.v a @% FStar.Int.pow2 16)})
assume val int32_to_int8 : a:i32 -> Tot (b:i8 {I8.v b  = (I32.v a @% FStar.Int.pow2 8)})

assume val int63_to_int64: a:i63 -> Tot (b:i64{I64.v b = I63.v a})
//assume val int63_to_int32: a:i63 -> Tot (b:i32{b = I32.int_to_int32 (I63.v a)})
//assume val int63_to_int16: a:i63 -> Tot (b:i16{b = I16.int_to_int16 (I63.v a)})
//assume val int63_to_int8: a:i63 -> Tot (b:i8{b = I8.int_to_int8 (I63.v a)})
assume val int63_to_int32: a:i63 -> Tot (b:i32{I32.v b = (I63.v a @% FStar.Int.pow2 32)})
assume val int63_to_int16: a:i63 -> Tot (b:i16{I16.v b = (I63.v a @% FStar.Int.pow2 16)})
assume val int63_to_int8 : a:i63 -> Tot (b:i8 {I8.v b  = (I63.v a @% FStar.Int.pow2 8)})

//assume val int64_to_int63: a:i64 -> Tot (b:i63{I63.v b = I63.int_to_int63 (U64.v a)})
//assume val int64_to_int32: a:i64 -> Tot (b:i32{I32.v b = U32.int_to_int32 (I64.v a})
//assume val int64_to_int16: a:i64 -> Tot (b:i16{I16.v b = I16.int_to_int16 (I64.v a})
//assume val int64_to_int8: a:i64 -> Tot (b:i8{I8.v b = I8.int_to_int8 (I64.v a})
assume val int64_to_int63: a:i64 -> Tot (b:i63{I63.v b = (I64.v a @% FStar.Int.pow2 63)})
assume val int64_to_int32: a:i64 -> Tot (b:i32{I32.v b = (I64.v a @% FStar.Int.pow2 32)})
assume val int64_to_int16: a:i64 -> Tot (b:i16{I16.v b = (I64.v a @% FStar.Int.pow2 16)})
assume val int64_to_int8 : a:i64 -> Tot (b:i8 {I8.v b  = (I64.v a @% FStar.Int.pow2 8)})

(** Uints to Ints **)
assume val uint8_to_int64: a:u8 -> Tot (b:i64{I64.v b = U8.v a})
assume val uint8_to_int63: a:u8 -> Tot (b:i63{I63.v b = U8.v a})
assume val uint8_to_int32: a:u8 -> Tot (b:i32{I32.v b = U8.v a})
assume val uint8_to_int16: a:u8 -> Tot (b:i16{I16.v b = U8.v a})
assume val uint8_to_int8 : a:u8 -> Tot (b:i8 {I8.v b  = (U8.v a @% FStar.Int.pow2 8)})

assume val uint16_to_int64: a:u16 -> Tot (b:i64{I64.v b = U16.v a})
assume val uint16_to_int63: a:u16 -> Tot (b:i63{I63.v b = U16.v a})
assume val uint16_to_int32: a:u16 -> Tot (b:i32{I32.v b = U16.v a})
//assume val uint16_to_int16: a:u16 -> Tot (b:u16{b = I16.int_to_int16 (U16.v a)})
//assume val uint16_to_int8: a:u16 -> Tot (b:u8{b = I8.int_to_int8 (U16.v a)})
assume val uint16_to_int16: a:u16 -> Tot (b:i16{I16.v b = (U16.v a @% FStar.Int.pow2 16)})
assume val uint16_to_int8 : a:u16 -> Tot (b:i8 {I8.v b  = (U16.v a @% FStar.Int.pow2 8)})

assume val uint32_to_int64: a:u32 -> Tot (b:i64{I64.v b = U32.v a})
assume val uint32_to_int63: a:u32 -> Tot (b:i63{I63.v b = U32.v a})
//assume val uint32_to_int32: a:u32 -> Tot (b:i32{b = I32.int_to_int32 (U32.v a)})
//assume val uint32_to_int16: a:u32 -> Tot (b:i16{b = I16.int_to_int16 (U32.v a)})
//assume val uint32_to_int8: a:u32 -> Tot (b:i8{b = I8.int_to_int8 (U32.v a)})
assume val uint32_to_int32: a:u32 -> Tot (b:i32{I32.v b = (U32.v a @% FStar.Int.pow2 32)})
assume val uint32_to_int16: a:u32 -> Tot (b:i16{I16.v b = (U32.v a @% FStar.Int.pow2 16)})
assume val uint32_to_int8 : a:u32 -> Tot (b:i8 {I8.v b  = (U32.v a @% FStar.Int.pow2 8)})

assume val uint63_to_int64: a:u63 -> Tot (b:i64{I64.v b = U63.v a})
//assume val uint63_to_int63: a:u63 -> Tot (b:i63{b = I63.int_to_int63 (U63.v a)})
//assume val uint63_to_int32: a:u63 -> Tot (b:i32{b = I32.int_to_int32 (U63.v a)})
//assume val uint63_to_int16: a:u63 -> Tot (b:i16{b = I16.int_to_int16 (U63.v a)})
//assume val uint63_to_int8: a:u63 -> Tot (b:i8{b = I8.int_to_int8 (U63.v a)})
assume val uint63_to_int63: a:u63 -> Tot (b:i63{I63.v b = (U63.v a @% FStar.Int.pow2 63)})
assume val uint63_to_int32: a:u63 -> Tot (b:i32{I32.v b = (U63.v a @% FStar.Int.pow2 32)})
assume val uint63_to_int16: a:u63 -> Tot (b:i16{I16.v b = (U63.v a @% FStar.Int.pow2 16)})
assume val uint63_to_int8 : a:u63 -> Tot (b:i8 {I8.v b  = (U63.v a @% FStar.Int.pow2 8)})

//assume val uint64_to_int64: a:u64 -> Tot (b:i64{I64.v b = I64.int_to_int64 (U64.v a)})
//assume val uint64_to_int63: a:u64 -> Tot (b:i63{I63.v b = I63.int_to_int63 (U64.v a)})
//assume val uint64_to_int32: a:u64 -> Tot (b:i32{I32.v b = U32.int_to_int32 (U64.v a})
//assume val uint64_to_int16: a:u64 -> Tot (b:i16{I16.v b = I16.int_to_int16 (U64.v a})
//assume val uint64_to_int8: a:u64 -> Tot (b:i8{I8.v b = I8.int_to_int8 (U64.v a})
assume val uint64_to_int64: a:u64 -> Tot (b:i64{I64.v b = (U64.v a @% FStar.Int.pow2 64)})
assume val uint64_to_int63: a:u64 -> Tot (b:i63{I63.v b = (U64.v a @% FStar.Int.pow2 63)})
assume val uint64_to_int32: a:u64 -> Tot (b:i32{I32.v b = (U64.v a @% FStar.Int.pow2 32)})
assume val uint64_to_int16: a:u64 -> Tot (b:i16{I16.v b = (U64.v a @% FStar.Int.pow2 16)})
assume val uint64_to_int8 : a:u64 -> Tot (b:i8 {I8.v b  = (U64.v a @% FStar.Int.pow2 8)})

(** Ints to uints *)
assume val int8_to_uint64: a:i8 -> Tot (b:u64{U64.v b = I8.v a % FStar.UInt.pow2 64})
assume val int8_to_uint63: a:i8 -> Tot (b:u63{U63.v b = I8.v a % FStar.UInt.pow2 63})
assume val int8_to_uint32: a:i8 -> Tot (b:u32{U32.v b = I8.v a % FStar.UInt.pow2 32})
assume val int8_to_uint16: a:i8 -> Tot (b:u16{U16.v b = I8.v a % FStar.UInt.pow2 16})
assume val int8_to_uint8 : a:i8 -> Tot (b:u8 {U8.v b  = I8.v a % FStar.UInt.pow2 8})

assume val int16_to_uint64: a:i16 -> Tot (b:u64{U64.v b = I16.v a % FStar.UInt.pow2 64})
assume val int16_to_uint63: a:i16 -> Tot (b:u63{U63.v b = I16.v a % FStar.UInt.pow2 63})
assume val int16_to_uint32: a:i16 -> Tot (b:u32{U32.v b = I16.v a % FStar.UInt.pow2 32})
assume val int16_to_uint16: a:i16 -> Tot (b:u16{U16.v b = I16.v a % FStar.UInt.pow2 16})
//assume val int16_to_uint16: a:i16 -> Tot (b:u16{b = U16.int_to_uint16 (I16.v a)})
//assume val int16_to_uint8: a:i16 -> Tot (b:u8{b = U8.int_to_uint8 (I16.v a)})
assume val int16_to_uint8 : a:i16 -> Tot (b:u8 {U8.v b  = I16.v a % FStar.UInt.pow2 8})

assume val int32_to_uint64: a:i32 -> Tot (b:u64{U64.v b = I32.v a % FStar.UInt.pow2 64})
assume val int32_to_uint63: a:i32 -> Tot (b:u63{U63.v b = I32.v a % FStar.UInt.pow2 63})
assume val int32_to_uint32: a:i32 -> Tot (b:u32{U32.v b = I32.v a % FStar.UInt.pow2 32})
//assume val int32_to_uint32: a:i32 -> Tot (b:u32{b = U32.int_to_uint32 (I32.v a)})
//assume val int32_to_uint16: a:i32 -> Tot (b:u16{b = U16.int_to_uint16 (I32.v a)})
//assume val int32_to_uint8: a:i32 -> Tot (b:u8{b = U8.int_to_uint8 (I32.v a)})
assume val int32_to_uint16: a:i32 -> Tot (b:u16{U16.v b = I32.v a % FStar.UInt.pow2 16})
assume val int32_to_uint8 : a:i32 -> Tot (b:u8 {U8.v b  = I32.v a % FStar.UInt.pow2 8})

assume val int63_to_uint64: a:i63 -> Tot (b:u64{U64.v b = I63.v a % FStar.UInt.pow2 64})
assume val int63_to_uint63: a:i63 -> Tot (b:u63{U63.v b = I63.v a % FStar.UInt.pow2 63})
//assume val int63_to_uint63: a:i63 -> Tot (b:u63{b = U63.int_to_uint63 (I63.v a)})
//assume val int63_to_uint32: a:i63 -> Tot (b:u32{b = U32.int_to_uint32 (I63.v a)})
//assume val int63_to_uint16: a:i63 -> Tot (b:u16{b = U16.int_to_uint16 (I63.v a)})
//assume val int63_to_uint8: a:i63 -> Tot (b:u8{b = U8.int_to_uint8 (I63.v a)})
assume val int63_to_uint32: a:i63 -> Tot (b:u32{U32.v b = I63.v a % FStar.UInt.pow2 32})
assume val int63_to_uint16: a:i63 -> Tot (b:u16{U16.v b = I63.v a % FStar.UInt.pow2 16})
assume val int63_to_uint8 : a:i63 -> Tot (b:u8 {U8.v b  = I63.v a % FStar.UInt.pow2 8})

//assume val int64_to_uint64: a:i64 -> Tot (b:u64{U64.v b = U64.int_to_uint63 (I64.v a)})
//assume val int64_to_uint63: a:i64 -> Tot (b:u63{U63.v b = U63.int_to_uint63 (I64.v a)})
//assume val int64_to_uint32: a:i64 -> Tot (b:u32{U32.v b = U32.int_to_uint32 (I64.v a})
//assume val int64_to_uint16: a:i64 -> Tot (b:u16{U16.v b = U16.int_to_uint16 (I64.v a})
//assume val int64_to_uint8: a:i64 -> Tot (b:u8{U8.v b = U8.int_to_uint8 (I64.v a})
assume val int64_to_uint64: a:i64 -> Tot (b:u64{U64.v b = I64.v a % FStar.UInt.pow2 64})
assume val int64_to_uint63: a:i64 -> Tot (b:u63{U63.v b = I64.v a % FStar.UInt.pow2 63})
assume val int64_to_uint32: a:i64 -> Tot (b:u32{U32.v b = I64.v a % FStar.UInt.pow2 32})
assume val int64_to_uint16: a:i64 -> Tot (b:u16{U16.v b = I64.v a % FStar.UInt.pow2 16})
assume val int64_to_uint8 : a:i64 -> Tot (b:u8 {U8.v b  = I64.v a % FStar.UInt.pow2 8})
