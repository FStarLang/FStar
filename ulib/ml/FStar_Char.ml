type nonrec char = char

let lowercase = BatChar.lowercase
let uppercase = BatChar.uppercase
let int_of_char x = BatChar.code x |> Z.of_int
let char_of_int x = BatChar.chr (Z.to_int x)
