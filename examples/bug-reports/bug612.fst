module Bug612

assume val f' : int -> int -> int -> Tot int
assume val g' : int -> int -> int -> Tot int

val l' : unit -> Lemma (requires (f 0 == g 0))
                       (ensures (f 0 1 == g 0 1))
let l' () = ()
