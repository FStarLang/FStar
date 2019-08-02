module UChar = BatUChar

type char = int[@@deriving yojson,show]

(* FIXME(adl) UChar.lowercase/uppercase removed from recent Batteries. Use Camomile? *)
let lowercase x = 
  try Char.code (Char.lowercase_ascii (Char.chr x))
  with _ -> x
let uppercase x =
  try Char.code (Char.uppercase_ascii (Char.chr x))
  with _ -> x
let int_of_char x = Z.of_int x
let char_of_int x = Z.to_int x
let u32_of_char x = x
