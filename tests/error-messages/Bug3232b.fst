module Bug3232b

inline_for_extraction
val f (x:int) : unit

[@@expect_failure]
noextract inline_for_extraction
let f x = ()
