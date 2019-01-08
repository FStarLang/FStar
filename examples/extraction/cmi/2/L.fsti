module L

type inttype = | U8

inline_for_extraction
val uint_t: inttype -> Type0

inline_for_extraction
let uint8 = uint_t U8

inline_for_extraction
val u8: (n:nat{n < 256}) -> uint8
