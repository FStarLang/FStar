module PositiveRelaxed

type nat =
  | O : nat
  | S : pre:nat -> nat

(* First, this inductive shouldn't be accepted by the _current_ check *)
(* Second, this inductive shouldn't be accepted by _any_ check *)
type p : nat -> Type =
  | PSO : (p O -> Tot (p (S O))) -> p (S O)
  | POd : p (S O) -> p O

val bad : p (S O) -> Tot (p (S O))
let bad h = let PSO f = h in f (POd h)

val loop : p (S O)
let loop = bad (PSO (fun h -> let POd h' = h in bad h'))

(* looooop ....

bad (PSO (fun h -> let POd h' = h in bad h')) ->           (unfold+match)
(fun h -> let POd h' = h in bad h')
  (POd (PSO (fun h -> let POd h' = h in bad h'))) ->       (beta+match)
bad (PSO (fun h -> let POd h' = h in bad h'))

 *)
