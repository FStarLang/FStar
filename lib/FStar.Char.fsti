module FStar.Char

new type char
val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot int
val char_of_int: n:int -> Tot (c:char{int_of_char c = n})
