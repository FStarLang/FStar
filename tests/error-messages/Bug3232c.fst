module Bug3232c

inline_for_extraction noextract
val f (x:int) : unit

[@@expect_failure]
noextract
let f x = ()
