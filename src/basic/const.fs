
module FStar.Const

type signedness = | Unsigned | Signed
type width = | Int8 | Int16 | Int32 | Int64

let string_of_int_qualifier = function
  | Unsigned, Int8 -> "FStar.UInt8.uint8"
  | Signed, Int8 -> "FStar.Int8.unt8"
  | Unsigned, Int16 -> "FStar.UInt16.uint16"
  | Signed, Int16 -> "FStar.Int16.int16"
  | Unsigned, Int32 -> "FStar.UInt32.uint32"
  | Signed, Int32 -> "FStar.Int32.int32"
  | Unsigned, Int64 -> "FStar.UInt64.uint64"
  | Signed, Int64 -> "FStar.Int64.int64"

type sconst =
  | Const_effect
  | Const_unit
  | Const_bool        of bool
  | Const_int         of string * (signedness * width) option (* When None, means "mathematical integer", i.e. Prims.int. *)
  | Const_char        of char
  | Const_float       of double
  | Const_bytearray   of array<byte> * Range.range
  | Const_string      of array<byte> * Range.range           (* unicode encoded, F#/Caml independent *)
  | Const_range       of Range.range                         (* not denotable by the programmer *)
