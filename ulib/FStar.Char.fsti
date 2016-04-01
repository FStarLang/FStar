module FStar.Char

private type char' = 
  | Char : int -> char'

type char = char'

val lowercase: char -> char
val uppercase: char -> char
val int_of_char: char -> Tot int
val char_of_int: int -> Tot char
