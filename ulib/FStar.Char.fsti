module FStar.Char

let char_code = n:nat{n < pow2 21}

private type char' =
  | Char : char_code -> char'

type char = FStar.UInt8.t

val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot char_code
val char_of_int: code:char_code -> Tot (c:char{int_of_char c = code})
