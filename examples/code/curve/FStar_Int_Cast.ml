
open Prims

type u8 =
FStar_UInt8.t


type u16 =
FStar_UInt16.t


type u32 =
FStar_UInt32.t


type u63 =
FStar_UInt63.t


type u64 =
FStar_UInt64.t


type u128 =
FStar_UInt128.t


type i8 =
FStar_Int8.t


type i16 =
FStar_Int16.t


type i32 =
FStar_Int32.t


type i63 =
FStar_Int63.t


type i64 =
FStar_Int64.t


let op_At_Percent : Prims.int  ->  Prims.int  ->  Prims.int = FStar_Int.op_At_Percent


let uint8_to_uint64 : u8  ->  u64 = (Obj.magic ((fun a -> ())))


let uint8_to_uint63 : u8  ->  u63 = (Obj.magic ((fun a -> ())))


let uint8_to_uint32 : u8  ->  u32 = (Obj.magic ((fun a -> ())))


let uint8_to_uint16 : u8  ->  u16 = (Obj.magic ((fun a -> ())))


let uint16_to_uint64 : u16  ->  u64 = (Obj.magic ((fun a -> ())))


let uint16_to_uint63 : u16  ->  u63 = (Obj.magic ((fun a -> ())))


let uint16_to_uint32 : u16  ->  u32 = (Obj.magic ((fun a -> ())))


let uint16_to_uint8 : u16  ->  u8 = (Obj.magic ((fun a -> ())))


let uint32_to_uint64 : u32  ->  u64 = (Obj.magic ((fun a -> ())))


let uint32_to_uint63 : u32  ->  u63 = (Obj.magic ((fun a -> ())))


let uint32_to_uint16 : u32  ->  u16 = (Obj.magic ((fun a -> ())))


let uint32_to_uint8 : u32  ->  u8 = (Obj.magic ((fun a -> ())))


let uint63_to_uint64 : u63  ->  u64 = (Obj.magic ((fun a -> ())))


let uint63_to_uint32 : u63  ->  u32 = (Obj.magic ((fun a -> ())))


let uint63_to_uint16 : u63  ->  u16 = (Obj.magic ((fun a -> ())))


let uint63_to_uint8 : u63  ->  u8 = (Obj.magic ((fun a -> ())))


let uint64_to_uint63 : u64  ->  u63 = (Obj.magic ((fun a -> ())))


let uint64_to_uint32 : u64  ->  u32 = (Obj.magic ((fun a -> ())))


let uint64_to_uint16 : u64  ->  u16 = (Obj.magic ((fun a -> ())))


let uint64_to_uint8 : u64  ->  u8 = (Obj.magic ((fun a -> ())))


let int8_to_int64 : i8  ->  i64 = (Obj.magic ((fun a -> ())))


let int8_to_int63 : i8  ->  i63 = (Obj.magic ((fun a -> ())))


let int8_to_int32 : i8  ->  i32 = (Obj.magic ((fun a -> ())))


let int8_to_int16 : i8  ->  i16 = (Obj.magic ((fun a -> ())))


let int16_to_int64 : i16  ->  i64 = (Obj.magic ((fun a -> ())))


let int16_to_int63 : i16  ->  i63 = (Obj.magic ((fun a -> ())))


let int16_to_int32 : i16  ->  i32 = (Obj.magic ((fun a -> ())))


let int16_to_int8 : i16  ->  i8 = (Obj.magic ((fun a -> ())))


let int32_to_int64 : i32  ->  i64 = (Obj.magic ((fun a -> ())))


let int32_to_int63 : i32  ->  i63 = (Obj.magic ((fun a -> ())))


let int32_to_int16 : i32  ->  i16 = (Obj.magic ((fun a -> ())))


let int32_to_int8 : i32  ->  i8 = (Obj.magic ((fun a -> ())))


let int63_to_int64 : i63  ->  i64 = (Obj.magic ((fun a -> ())))


let int63_to_int32 : i63  ->  i32 = (Obj.magic ((fun a -> ())))


let int63_to_int16 : i63  ->  i16 = (Obj.magic ((fun a -> ())))


let int63_to_int8 : i63  ->  i8 = (Obj.magic ((fun a -> ())))


let int64_to_int63 : i64  ->  i63 = (Obj.magic ((fun a -> ())))


let int64_to_int32 : i64  ->  i32 = (Obj.magic ((fun a -> ())))


let int64_to_int16 : i64  ->  i16 = (Obj.magic ((fun a -> ())))


let int64_to_int8 : i64  ->  i8 = (Obj.magic ((fun a -> ())))


let uint8_to_int64 : u8  ->  i64 = (Obj.magic ((fun a -> ())))


let uint8_to_int63 : u8  ->  i63 = (Obj.magic ((fun a -> ())))


let uint8_to_int32 : u8  ->  i32 = (Obj.magic ((fun a -> ())))


let uint8_to_int16 : u8  ->  i16 = (Obj.magic ((fun a -> ())))


let uint8_to_int8 : u8  ->  i8 = (Obj.magic ((fun a -> ())))


let uint16_to_int64 : u16  ->  i64 = (Obj.magic ((fun a -> ())))


let uint16_to_int63 : u16  ->  i63 = (Obj.magic ((fun a -> ())))


let uint16_to_int32 : u16  ->  i32 = (Obj.magic ((fun a -> ())))


let uint16_to_int16 : u16  ->  i16 = (Obj.magic ((fun a -> ())))


let uint16_to_int8 : u16  ->  i8 = (Obj.magic ((fun a -> ())))


let uint32_to_int64 : u32  ->  i64 = (Obj.magic ((fun a -> ())))


let uint32_to_int63 : u32  ->  i63 = (Obj.magic ((fun a -> ())))


let uint32_to_int32 : u32  ->  i32 = (Obj.magic ((fun a -> ())))


let uint32_to_int16 : u32  ->  i16 = (Obj.magic ((fun a -> ())))


let uint32_to_int8 : u32  ->  i8 = (Obj.magic ((fun a -> ())))


let uint63_to_int64 : u63  ->  i64 = (Obj.magic ((fun a -> ())))


let uint63_to_int63 : u63  ->  i63 = (Obj.magic ((fun a -> ())))


let uint63_to_int32 : u63  ->  i32 = (Obj.magic ((fun a -> ())))


let uint63_to_int16 : u63  ->  i16 = (Obj.magic ((fun a -> ())))


let uint63_to_int8 : u63  ->  i8 = (Obj.magic ((fun a -> ())))


let uint64_to_int64 : u64  ->  i64 = (Obj.magic ((fun a -> ())))


let uint64_to_int63 : u64  ->  i63 = (Obj.magic ((fun a -> ())))


let uint64_to_int32 : u64  ->  i32 = (Obj.magic ((fun a -> ())))


let uint64_to_int16 : u64  ->  i16 = (Obj.magic ((fun a -> ())))


let uint64_to_int8 : u64  ->  i8 = (Obj.magic ((fun a -> ())))


let int8_to_uint64 : i8  ->  u64 = (Obj.magic ((fun a -> ())))


let int8_to_uint63 : i8  ->  u63 = (Obj.magic ((fun a -> ())))


let int8_to_uint32 : i8  ->  u32 = (Obj.magic ((fun a -> ())))


let int8_to_uint16 : i8  ->  u16 = (Obj.magic ((fun a -> ())))


let int8_to_uint8 : i8  ->  u8 = (Obj.magic ((fun a -> ())))


let int16_to_uint64 : i16  ->  u64 = (Obj.magic ((fun a -> ())))


let int16_to_uint63 : i16  ->  u63 = (Obj.magic ((fun a -> ())))


let int16_to_uint32 : i16  ->  u32 = (Obj.magic ((fun a -> ())))


let int16_to_uint16 : i16  ->  u16 = (Obj.magic ((fun a -> ())))


let int16_to_uint8 : i16  ->  u8 = (Obj.magic ((fun a -> ())))


let int32_to_uint64 : i32  ->  u64 = (Obj.magic ((fun a -> ())))


let int32_to_uint63 : i32  ->  u63 = (Obj.magic ((fun a -> ())))


let int32_to_uint32 : i32  ->  u32 = (Obj.magic ((fun a -> ())))


let int32_to_uint16 : i32  ->  u16 = (Obj.magic ((fun a -> ())))


let int32_to_uint8 : i32  ->  u8 = (Obj.magic ((fun a -> ())))


let int63_to_uint64 : i63  ->  u64 = (Obj.magic ((fun a -> ())))


let int63_to_uint63 : i63  ->  u63 = (Obj.magic ((fun a -> ())))


let int63_to_uint32 : i63  ->  u32 = (Obj.magic ((fun a -> ())))


let int63_to_uint16 : i63  ->  u16 = (Obj.magic ((fun a -> ())))


let int63_to_uint8 : i63  ->  u8 = (Obj.magic ((fun a -> ())))


let int64_to_uint64 : i64  ->  u64 = (Obj.magic ((fun a -> ())))


let int64_to_uint63 : i64  ->  u63 = (Obj.magic ((fun a -> ())))


let int64_to_uint32 : i64  ->  u32 = (Obj.magic ((fun a -> ())))


let int64_to_uint16 : i64  ->  u16 = (Obj.magic ((fun a -> ())))


let int64_to_uint8 : i64  ->  u8 = (Obj.magic ((fun a -> ())))


let uint128_to_uint64 : u128  ->  u64 = (Obj.magic ((fun a -> ())))


let uint64_to_uint128 : u64  ->  u128 = (Obj.magic ((fun a -> ())))




