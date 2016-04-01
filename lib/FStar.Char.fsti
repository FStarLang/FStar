module FStar.Char

private type char' = 
  | Char : int -> char'
opaque type char = char'
val lowercase: char -> Tot char
val uppercase: char -> Tot char
val int_of_char: char -> Tot int
val char_of_int: n:int -> Tot (c:char{int_of_char c = n})
