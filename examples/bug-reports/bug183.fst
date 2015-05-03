module Bug183

type test : Type = | T : x:bool -> test

val f : test -> bool
let f h = match h with T (t : int) -> t
