module FStar.Char

type char_code = n:nat{n < pow2 32}
type char = FStar.UInt32.t

val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot char_code
val char_of_int: code:char_code -> Tot (c:char{int_of_char c = code})
