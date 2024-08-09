module Test.FStar.Parse

open FStar.Parse

let _ = assert (int_of_string "" == None)
let _ = assert (int_of_string "1" == Some 1)
let _ = assert (int_of_string "-1" == Some (-1))
let _ = assert (int_of_string "1234567890" == Some 1234567890)

let _ = assert (int_of_string "15x1" == None)
let _ = assert (int_of_string "x1" == None)

// Hex and binary also work.
let _ = assert (int_of_string "0x100" == Some 256)
let _ = assert (int_of_string "0b100" == Some 4)
