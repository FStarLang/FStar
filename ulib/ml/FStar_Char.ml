type nonrec char = UChar.t

let lowercase = UChar.lowercase
let uppercase = UChar.uppercase
let int_of_char x = UChar.code x |> Z.of_int
let char_of_int x = UChar.chr (Z.to_int x)
