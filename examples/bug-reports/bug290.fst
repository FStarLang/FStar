module Bug290

val id : nat -> Tot nat
let id x = x

assume val test : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (fst r) = fst r)) (*Succeeds*)

assume val test2 : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (snd r) = snd r)) (*Succeeds*)

assume val test3 : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (fst r) = snd r)) (*Fails*)

assume val test4 : unit -> Pure (nat*nat)
                               (requires  True)
                               (ensures  (fun r -> id (snd r) = fst r)) (*Fails*)

