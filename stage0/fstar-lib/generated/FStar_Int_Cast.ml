open Prims
let (op_At_Percent : Prims.int -> Prims.int -> Prims.int) =
  FStar_Int.op_At_Percent
let (uint8_to_uint64 : FStar_UInt8.t -> FStar_UInt64.t) =
  fun a -> FStar_UInt64.uint_to_t (FStar_UInt8.v a)
let (uint8_to_uint32 : FStar_UInt8.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (FStar_UInt8.v x)
let (uint8_to_uint16 : FStar_UInt8.t -> FStar_UInt16.t) =
  fun x -> FStar_UInt16.uint_to_t (FStar_UInt8.v x)
let (uint16_to_uint64 : FStar_UInt16.t -> FStar_UInt64.t) =
  fun x -> FStar_UInt64.uint_to_t (FStar_UInt16.v x)
let (uint16_to_uint32 : FStar_UInt16.t -> FStar_UInt32.t) =
  fun x -> FStar_UInt32.uint_to_t (FStar_UInt16.v x)
let (uint16_to_uint8 : FStar_UInt16.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_UInt16.v x) mod (Prims.pow2 (Prims.of_int (8))))
let (uint32_to_uint64 : FStar_UInt32.t -> FStar_UInt64.t) =
  fun x -> FStar_UInt64.uint_to_t (FStar_UInt32.v x)
let (uint32_to_uint16 : FStar_UInt32.t -> FStar_UInt16.t) =
  fun x ->
    FStar_UInt16.uint_to_t
      ((FStar_UInt32.v x) mod (Prims.pow2 (Prims.of_int (16))))
let (uint32_to_uint8 : FStar_UInt32.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_UInt32.v x) mod (Prims.pow2 (Prims.of_int (8))))
let (uint64_to_uint32 : FStar_UInt64.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.uint_to_t
      ((FStar_UInt64.v x) mod (Prims.pow2 (Prims.of_int (32))))
let (uint64_to_uint16 : FStar_UInt64.t -> FStar_UInt16.t) =
  fun x ->
    FStar_UInt16.uint_to_t
      ((FStar_UInt64.v x) mod (Prims.pow2 (Prims.of_int (16))))
let (uint64_to_uint8 : FStar_UInt64.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_UInt64.v x) mod (Prims.pow2 (Prims.of_int (8))))
let (int8_to_int64 : FStar_Int8.t -> FStar_Int64.t) =
  fun x -> FStar_Int64.int_to_t (FStar_Int8.v x)
let (int8_to_int32 : FStar_Int8.t -> FStar_Int32.t) =
  fun x -> FStar_Int32.int_to_t (FStar_Int8.v x)
let (int8_to_int16 : FStar_Int8.t -> FStar_Int16.t) =
  fun x -> FStar_Int16.int_to_t (FStar_Int8.v x)
let (int16_to_int64 : FStar_Int16.t -> FStar_Int64.t) =
  fun x ->
    FStar_Int64.int_to_t
      (op_At_Percent (FStar_Int16.v x) (Prims.pow2 (Prims.of_int (64))))
let (int16_to_int32 : FStar_Int16.t -> FStar_Int32.t) =
  fun x ->
    FStar_Int32.int_to_t
      (op_At_Percent (FStar_Int16.v x) (Prims.pow2 (Prims.of_int (32))))
let (int16_to_int8 : FStar_Int16.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_Int16.v x) (Prims.pow2 (Prims.of_int (8))))
let (int32_to_int64 : FStar_Int32.t -> FStar_Int64.t) =
  fun x ->
    FStar_Int64.int_to_t
      (op_At_Percent (FStar_Int32.v x) (Prims.pow2 (Prims.of_int (64))))
let (int32_to_int16 : FStar_Int32.t -> FStar_Int16.t) =
  fun x ->
    FStar_Int16.int_to_t
      (op_At_Percent (FStar_Int32.v x) (Prims.pow2 (Prims.of_int (16))))
let (int32_to_int8 : FStar_Int32.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_Int32.v x) (Prims.pow2 (Prims.of_int (8))))
let (int64_to_int32 : FStar_Int64.t -> FStar_Int32.t) =
  fun x ->
    FStar_Int32.int_to_t
      (op_At_Percent (FStar_Int64.v x) (Prims.pow2 (Prims.of_int (32))))
let (int64_to_int16 : FStar_Int64.t -> FStar_Int16.t) =
  fun x ->
    FStar_Int16.int_to_t
      (op_At_Percent (FStar_Int64.v x) (Prims.pow2 (Prims.of_int (16))))
let (int64_to_int8 : FStar_Int64.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_Int64.v x) (Prims.pow2 (Prims.of_int (8))))
let (uint8_to_int64 : FStar_UInt8.t -> FStar_Int64.t) =
  fun x -> FStar_Int64.int_to_t (FStar_UInt8.v x)
let (uint8_to_int32 : FStar_UInt8.t -> FStar_Int32.t) =
  fun x -> FStar_Int32.int_to_t (FStar_UInt8.v x)
let (uint8_to_int16 : FStar_UInt8.t -> FStar_Int16.t) =
  fun x -> FStar_Int16.int_to_t (FStar_UInt8.v x)
let (uint8_to_int8 : FStar_UInt8.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_UInt8.v x) (Prims.pow2 (Prims.of_int (8))))
let (uint16_to_int64 : FStar_UInt16.t -> FStar_Int64.t) =
  fun x -> FStar_Int64.int_to_t (FStar_UInt16.v x)
let (uint16_to_int32 : FStar_UInt16.t -> FStar_Int32.t) =
  fun x -> FStar_Int32.int_to_t (FStar_UInt16.v x)
let (uint16_to_int16 : FStar_UInt16.t -> FStar_Int16.t) =
  fun x ->
    FStar_Int16.int_to_t
      (op_At_Percent (FStar_UInt16.v x) (Prims.pow2 (Prims.of_int (16))))
let (uint16_to_int8 : FStar_UInt16.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_UInt16.v x) (Prims.pow2 (Prims.of_int (8))))
let (uint32_to_int64 : FStar_UInt32.t -> FStar_Int64.t) =
  fun x -> FStar_Int64.int_to_t (FStar_UInt32.v x)
let (uint32_to_int32 : FStar_UInt32.t -> FStar_Int32.t) =
  fun x ->
    FStar_Int32.int_to_t
      (op_At_Percent (FStar_UInt32.v x) (Prims.pow2 (Prims.of_int (32))))
let (uint32_to_int16 : FStar_UInt32.t -> FStar_Int16.t) =
  fun x ->
    FStar_Int16.int_to_t
      (op_At_Percent (FStar_UInt32.v x) (Prims.pow2 (Prims.of_int (16))))
let (uint32_to_int8 : FStar_UInt32.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_UInt32.v x) (Prims.pow2 (Prims.of_int (8))))
let (uint64_to_int64 : FStar_UInt64.t -> FStar_Int64.t) =
  fun x ->
    FStar_Int64.int_to_t
      (op_At_Percent (FStar_UInt64.v x) (Prims.pow2 (Prims.of_int (64))))
let (uint64_to_int32 : FStar_UInt64.t -> FStar_Int32.t) =
  fun x ->
    FStar_Int32.int_to_t
      (op_At_Percent (FStar_UInt64.v x) (Prims.pow2 (Prims.of_int (32))))
let (uint64_to_int16 : FStar_UInt64.t -> FStar_Int16.t) =
  fun x ->
    FStar_Int16.int_to_t
      (op_At_Percent (FStar_UInt64.v x) (Prims.pow2 (Prims.of_int (16))))
let (uint64_to_int8 : FStar_UInt64.t -> FStar_Int8.t) =
  fun x ->
    FStar_Int8.int_to_t
      (op_At_Percent (FStar_UInt64.v x) (Prims.pow2 (Prims.of_int (8))))
let (int8_to_uint64 : FStar_Int8.t -> FStar_UInt64.t) =
  fun x ->
    FStar_UInt64.uint_to_t
      ((FStar_Int8.v x) mod (Prims.pow2 (Prims.of_int (64))))
let (int8_to_uint32 : FStar_Int8.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.uint_to_t
      ((FStar_Int8.v x) mod (Prims.pow2 (Prims.of_int (32))))
let (int8_to_uint16 : FStar_Int8.t -> FStar_UInt16.t) =
  fun x ->
    FStar_UInt16.uint_to_t
      ((FStar_Int8.v x) mod (Prims.pow2 (Prims.of_int (16))))
let (int8_to_uint8 : FStar_Int8.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_Int8.v x) mod (Prims.pow2 (Prims.of_int (8))))
let (int16_to_uint64 : FStar_Int16.t -> FStar_UInt64.t) =
  fun x ->
    FStar_UInt64.uint_to_t
      ((FStar_Int16.v x) mod (Prims.pow2 (Prims.of_int (64))))
let (int16_to_uint32 : FStar_Int16.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.uint_to_t
      ((FStar_Int16.v x) mod (Prims.pow2 (Prims.of_int (32))))
let (int16_to_uint16 : FStar_Int16.t -> FStar_UInt16.t) =
  fun x ->
    FStar_UInt16.uint_to_t
      ((FStar_Int16.v x) mod (Prims.pow2 (Prims.of_int (16))))
let (int16_to_uint8 : FStar_Int16.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_Int16.v x) mod (Prims.pow2 (Prims.of_int (8))))
let (int32_to_uint64 : FStar_Int32.t -> FStar_UInt64.t) =
  fun x ->
    FStar_UInt64.uint_to_t
      ((FStar_Int32.v x) mod (Prims.pow2 (Prims.of_int (64))))
let (int32_to_uint32 : FStar_Int32.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.uint_to_t
      ((FStar_Int32.v x) mod (Prims.pow2 (Prims.of_int (32))))
let (int32_to_uint16 : FStar_Int32.t -> FStar_UInt16.t) =
  fun x ->
    FStar_UInt16.uint_to_t
      ((FStar_Int32.v x) mod (Prims.pow2 (Prims.of_int (16))))
let (int32_to_uint8 : FStar_Int32.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_Int32.v x) mod (Prims.pow2 (Prims.of_int (8))))
let (int64_to_uint64 : FStar_Int64.t -> FStar_UInt64.t) =
  fun x ->
    FStar_UInt64.uint_to_t
      ((FStar_Int64.v x) mod (Prims.pow2 (Prims.of_int (64))))
let (int64_to_uint32 : FStar_Int64.t -> FStar_UInt32.t) =
  fun x ->
    FStar_UInt32.uint_to_t
      ((FStar_Int64.v x) mod (Prims.pow2 (Prims.of_int (32))))
let (int64_to_uint16 : FStar_Int64.t -> FStar_UInt16.t) =
  fun x ->
    FStar_UInt16.uint_to_t
      ((FStar_Int64.v x) mod (Prims.pow2 (Prims.of_int (16))))
let (int64_to_uint8 : FStar_Int64.t -> FStar_UInt8.t) =
  fun x ->
    FStar_UInt8.uint_to_t
      ((FStar_Int64.v x) mod (Prims.pow2 (Prims.of_int (8))))