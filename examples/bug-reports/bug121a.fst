module Bug121a

val apply : ('a -> Tot 'b) -> 'a -> Tot 'b
let apply f x = f x

val dec : nat -> Tot nat
let rec dec x =
  match x with
  | 0 -> 0
  | _ -> 1 + apply dec (x-1)

val should_be_trivial : x:nat{x>0} -> Lemma
  (ensures (dec x = 1 + apply dec (x-1)))
let should_be_trivial x = ()
