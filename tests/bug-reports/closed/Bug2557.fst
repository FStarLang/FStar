module Bug2557

// 0x0000 - 0xD799 are valid characters
let _ = Char.char_of_int 0xD799

// 0xD800 - 0xDFFF are invalid characters (reserved for UTF-16 encoding)
[@@expect_failure]
let _ = Char.char_of_int 0xD800

[@@expect_failure]
let _ = Char.char_of_int 0xDFFF

// 0xE000 - 0x10FFFF are valid characters
let _ = Char.char_of_int 0xE000

let _ = Char.char_of_int 0x10FFFF

// 0x110000-inf are invalid characters
[@@expect_failure]
let _ = Char.char_of_int 0x110000
