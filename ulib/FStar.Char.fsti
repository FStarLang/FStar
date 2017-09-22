module FStar.Char

module U32 = FStar.UInt32

type char_code = n:nat{n < pow2 21}
type char = n:U32.t{U32.v n < pow2 21}

val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot char_code
val char_of_int: code:char_code -> Tot (c:char{int_of_char c = code})
