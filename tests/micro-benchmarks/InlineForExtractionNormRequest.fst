module InlineForExtractionNormRequest

inline_for_extraction
let id (x:'a) = x

let test (x:int) = norm [primops] (id 0 + 1)
