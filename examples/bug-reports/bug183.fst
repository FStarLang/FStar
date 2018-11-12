module Bug183

type test : Type = | T : x:bool -> test

(* this should fail, or at least raise a warning *)
val f : test -> bool
let f h = match h with | T (t : int) -> t
