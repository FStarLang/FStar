module FStar.Char

assume new type char: Type0

val lowercase: char -> char
val uppercase: char -> char
val int_of_char: char -> Tot int
val char_of_int: int -> Tot char
