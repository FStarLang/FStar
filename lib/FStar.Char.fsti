module FStar.Char

abstract new type char
val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot int
val char_of_int: int -> Tot char
