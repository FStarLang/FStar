module TEST

(* type nat = int *) (*makes it succeed*)
val id : nat -> Tot nat
let id x = x

val test : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (fst r) = snd r)) (*Fails*)
(*
                               (ensures  (fun r -> id (fst r) = fst r)) (*Succeeds*)
                               (ensures  (fun r -> id (snd r) = fst r)) (*Fails*)
                               (ensures  (fun r -> id (snd r) = snd r)) (*Succeeds*)
*)
let test () = 0,0
