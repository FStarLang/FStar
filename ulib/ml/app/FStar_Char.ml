module UChar = BatUChar
module U32 = FStar_UInt32
open FStar_Char_Type

type char_code = U32.t

let u32_of_char (x:char) : char_code = U32.of_native_int x
let char_of_u32 (x:char_code) : char = U32.to_native_int x

(* FIXME(adl) UChar.lowercase/uppercase removed from recent Batteries. Use Camomile? *)
let lowercase (x:char) : char =
  try Char.code (Char.lowercase_ascii (Char.chr x))
  with _ -> x

let uppercase (x:char) : char =
  try Char.code (Char.uppercase_ascii (Char.chr x))
  with _ -> x
