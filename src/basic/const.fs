
module FStar.Const

open FStar.BaseTypes

type signedness = | Unsigned | Signed
type width = | Int8 | Int16 | Int32 | Int64

type sconst =
  | Const_effect
  | Const_unit
  | Const_bool        of bool
  | Const_int         of string * option<(signedness * width)> (* When None, means "mathematical integer", i.e. Prims.int. *)
  | Const_char        of char
  | Const_float       of double
  | Const_bytearray   of array<byte> * Range.range
  | Const_string      of array<byte> * Range.range           (* unicode encoded, F#/Caml independent *)
  | Const_range       of Range.range                         (* not denotable by the programmer *)
  | Const_reify                                              (* a coercion from a computation to a Tot term *)
  | Const_reflect                                            (* a coercion from a Tot term to a computation *)