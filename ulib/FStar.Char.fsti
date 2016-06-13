module FStar.Char

private type char' =
  | Char : int -> char'

type char = char'

val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot int
val char_of_int: int -> Tot char // Cannot be total and inverse of int_of_char/injective
