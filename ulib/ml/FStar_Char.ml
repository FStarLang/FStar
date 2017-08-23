module UChar = BatUChar
type nonrec char = UChar.t

(* FIXME(adl) UChar.lowercase/uppercase removed from recent Batteries. Use Camomile? *)
let lowercase x = if UChar.is_ascii x then UChar.of_char (Char.lowercase (UChar.char_of x)) else x
let uppercase x = if UChar.is_ascii x then UChar.of_char (Char.uppercase (UChar.char_of x)) else x
let int_of_char x = UChar.code x |> Z.of_int
let char_of_int x = UChar.chr (Z.to_int x)
