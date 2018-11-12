module Bug613

assume val f : int -> int -> Tot int
assume val g : int -> int -> Tot int

val l : unit -> Lemma (requires (f == g))
                      (ensures (f 0 1 == g 0 1))
let l () = () (* this works *)

val l' : unit -> Lemma (requires (f 0 == g 0))
                       (ensures (f 0 1 == g 0 1))
let l' () = () (* this fails *)

(* closer to mac.fst *)
assume val h : int -> Tot int
val l'' : unit -> Lemma (requires (f 0 == h))
                       (ensures (f 0 1 == h 1))
let l'' () = () (* this fails too *)

assume val i0: int -> Tot int
assume val i1: int -> Tot int
let test_i () : Lemma (requires i0==i1) (ensures i0 0 == i1 0) = ()
