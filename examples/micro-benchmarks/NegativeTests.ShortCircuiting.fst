module NegativeTests.ShortCircuiting

assume type bad_p : bool -> Type
val bad : x:int -> Tot (b:bool{bad_p b})
[@ (expect_failure [19])]
let rec bad x = true || bad (x-1)

val ff : unit -> Lemma (ensures False)
[@ (expect_failure [19])]
let ff u = ignore (false && (0 = 1))
