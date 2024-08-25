type char = int[@@deriving yojson,show]

let int_of_char (x:char) : Z.t = Z.of_int x
let char_of_int (i:Z.t) : char = Z.to_int i
