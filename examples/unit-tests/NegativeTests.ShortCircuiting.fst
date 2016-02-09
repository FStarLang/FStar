module NegativeTests.ShortCircuiting

type Bad : bool -> Type
val bad : x:int -> Tot (b:bool{Bad b})
let rec bad x = true || bad (x-1)

val ff : unit -> Lemma (ensures False)
let ff u = ignore (false && (0 = 1))
