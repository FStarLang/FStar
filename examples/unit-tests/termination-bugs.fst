module TerminationBugs

type nat =
  | O : nat
  | S : nat -> nat

(* CH: this seems like a bug in termination checking *)
val t1 : nat -> Tot bool
let rec t1 n =
  match n with
  | O        -> true
  | S O      -> false
  | S (S n') -> t1 (S (S n'))

(* CH: Same things here *)
val plus : nat -> nat -> Tot nat
let rec plus n m =
  match n with
    | O -> m
    | S O -> m
    | S (S n') -> plus (S (S n')) m

(* CH: maybe it's just a bug in pattern matching though?  This one is
   not exhaustive; could it be that O is for some reason not treated
   at a constructor? *)
val plus' : nat -> nat -> Tot nat
let plus' n m =
  match n with
    | O -> m
    | S O -> m

(* CH: Same problem here? *)
val minus : nat -> nat -> Tot nat
let rec minus (n : nat) (m : nat) : nat =
  match n, m with
  | O   , _    -> O
  | S n', m' -> minus (S n') m'

(* CH: Same problem here? *)
val xxx : nat -> Tot nat
let rec xxx (n : nat) : nat =
  match n, 42 with
  | O, 42   -> O
  | S n', 42 -> xxx (S n')

