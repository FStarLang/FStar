module Bug3232d

inline_for_extraction
val f (x:int) : unit

[@@expect_failure]
noextract
let f x = ()
