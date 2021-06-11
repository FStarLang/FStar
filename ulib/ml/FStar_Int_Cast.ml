let uint8_to_uint64 (x:int) : Stdint.Uint64.t =
  Stdint.Uint8.to_uint64 (Stdint.Uint8.of_int x)

let uint8_to_uint32 (x:int) : Stdint.Uint32.t =
  Stdint.Uint8.to_uint32 (Stdint.Uint8.of_int x)

let uint8_to_uint16 (x:int) : Stdint.Uint16.t =
  Stdint.Uint8.to_uint16 (Stdint.Uint8.of_int x)

let uint16_to_uint64 (x:Stdint.Uint16.t) : Stdint.Uint64.t = Stdint.Uint16.to_uint64 x

let uint16_to_uint32 (x:Stdint.Uint16.t) : Stdint.Uint32.t = Stdint.Uint16.to_uint32 x

let uint16_to_uint8 (x:Stdint.Uint16.t) : int =
  Stdint.Uint8.to_int (Stdint.Uint16.to_uint8 x)

let uint32_to_uint64 (x:Stdint.Uint32.t) : Stdint.Uint64.t = Stdint.Uint32.to_uint64 x

let uint32_to_uint16 (x:Stdint.Uint32.t) : Stdint.Uint16.t = Stdint.Uint32.to_uint16 x

let uint32_to_uint8 (x:Stdint.Uint32.t) : int =
   Stdint.Uint8.to_int (Stdint.Uint32.to_uint8 x)

let uint64_to_uint32 (x:Stdint.Uint64.t) : Stdint.Uint32.t = Stdint.Uint64.to_uint32 x

let uint64_to_uint16 (x:Stdint.Uint64.t) : Stdint.Uint16.t = Stdint.Uint64.to_uint16 x

let uint64_to_uint8 (x:Stdint.Uint64.t) : int =
   Stdint.Uint8.to_int (Stdint.Uint64.to_uint8 x)

let int8_to_int64 (x:Stdint.Int8.t) : Stdint.Int64.t = Stdint.Int8.to_int64 x

let int8_to_int32 (x:Stdint.Int8.t) : Stdint.Int32.t = Stdint.Int8.to_int32 x

let int8_to_int16 (x:Stdint.Int8.t) : Stdint.Int16.t = Stdint.Int8.to_int16 x

let int16_to_int64 (x:Stdint.Int16.t) : Stdint.Int64.t = Stdint.Int16.to_int64 x

let int16_to_int32 (x:Stdint.Int16.t) : Stdint.Int32.t = Stdint.Int16.to_int32 x

let int16_to_int8 (x:Stdint.Int16.t) : Stdint.Int8.t = Stdint.Int16.to_int8 x

let int32_to_int64 (x:Stdint.Int32.t) : Stdint.Int64.t = Stdint.Int32.to_int64 x

let int32_to_int16 (x:Stdint.Int32.t) : Stdint.Int16.t = Stdint.Int32.to_int16 x

let int32_to_int8 (x:Stdint.Int32.t) : Stdint.Int8.t = Stdint.Int32.to_int8 x

let int64_to_int32 (x:Stdint.Int64.t) : Stdint.Int32.t = Stdint.Int64.to_int32 x

let int64_to_int16 (x:Stdint.Int64.t) : Stdint.Int16.t = Stdint.Int64.to_int16 x

let int64_to_int8 (x:Stdint.Int64.t) : Stdint.Int8.t = Stdint.Int64.to_int8 x

let uint8_to_int64 (x:int) : Stdint.Int64.t =
  Stdint.Uint8.to_int64 (Stdint.Uint8.of_int x)

let uint8_to_int32 (x:int) : Stdint.Int32.t =
  Stdint.Uint8.to_int32 (Stdint.Uint8.of_int x)

let uint8_to_int16 (x:int) : Stdint.Int16.t =
  Stdint.Uint8.to_int16 (Stdint.Uint8.of_int x)

let uint8_to_int8 (x:int) : Stdint.Int8.t =
  Stdint.Uint8.to_int8 (Stdint.Uint8.of_int x)

let uint16_to_int64 (x:Stdint.Uint16.t) : Stdint.Int64.t = Stdint.Uint16.to_int64 x

let uint16_to_int32 (x:Stdint.Uint16.t) : Stdint.Int32.t = Stdint.Uint16.to_int32 x

let uint16_to_int16 (x:Stdint.Uint16.t) : Stdint.Int16.t = Stdint.Uint16.to_int16 x

let uint16_to_int8 (x:Stdint.Uint16.t) : Stdint.Int8.t = Stdint.Uint16.to_int8 x

let uint32_to_int64 (x:Stdint.Uint32.t) : Stdint.Int64.t = Stdint.Uint32.to_int64 x

let uint32_to_int32 (x:Stdint.Uint32.t) : Stdint.Int32.t = Stdint.Uint32.to_int32 x

let uint32_to_int16 (x:Stdint.Uint32.t) : Stdint.Int16.t = Stdint.Uint32.to_int16 x

let uint32_to_int8 (x:Stdint.Uint32.t) : Stdint.Int8.t = Stdint.Uint32.to_int8 x

let uint64_to_int64 (x:Stdint.Uint64.t) : Stdint.Int64.t = Stdint.Uint64.to_int64 x

let uint64_to_int32 (x:Stdint.Uint64.t) : Stdint.Int32.t = Stdint.Uint64.to_int32 x

let uint64_to_int16 (x:Stdint.Uint64.t) : Stdint.Int16.t = Stdint.Uint64.to_int16 x

let uint64_to_int8 (x:Stdint.Uint64.t) : Stdint.Int8.t = Stdint.Uint64.to_int8 x

let int8_to_uint64 (x:Stdint.Int8.t) : Stdint.Uint64.t = Stdint.Int8.to_uint64 x

let int8_to_uint32 (x:Stdint.Int8.t) : Stdint.Uint32.t = Stdint.Int8.to_uint32 x

let int8_to_uint16 (x:Stdint.Int8.t) : Stdint.Uint16.t = Stdint.Int8.to_uint16 x

let int8_to_uint8 (x:Stdint.Int8.t) : int =
  Stdint.Uint8.to_int (Stdint.Int8.to_uint8 x)

let int16_to_uint64 (x:Stdint.Int16.t) : Stdint.Uint64.t = Stdint.Int16.to_uint64 x

let int16_to_uint32 (x:Stdint.Int16.t) : Stdint.Uint32.t = Stdint.Int16.to_uint32 x

let int16_to_uint16 (x:Stdint.Int16.t) : Stdint.Uint16.t = Stdint.Int16.to_uint16 x

let int16_to_uint8 (x:Stdint.Int16.t) : int =
  Stdint.Uint8.to_int (Stdint.Int16.to_uint8 x)

let int32_to_uint64 (x:Stdint.Int32.t) : Stdint.Uint64.t = Stdint.Int32.to_uint64 x

let int32_to_uint32 (x:Stdint.Int32.t) : Stdint.Uint32.t = Stdint.Int32.to_uint32 x

let int32_to_uint16 (x:Stdint.Int32.t) : Stdint.Uint16.t = Stdint.Int32.to_uint16 x

let int32_to_uint8 (x:Stdint.Int32.t) : int =
  Stdint.Uint8.to_int (Stdint.Int32.to_uint8 x)

let int64_to_uint64 (x:Stdint.Int64.t) : Stdint.Uint64.t = Stdint.Int64.to_uint64 x

let int64_to_uint32 (x:Stdint.Int64.t) : Stdint.Uint32.t = Stdint.Int64.to_uint32 x

let int64_to_uint16 (x:Stdint.Int64.t) : Stdint.Uint16.t = Stdint.Int64.to_uint16 x

let int64_to_uint8 (x:Stdint.Int64.t) : int =
  Stdint.Uint8.to_int (Stdint.Int64.to_uint8 x)
