module PositiveRelaxed

type nat =
  | O : nat
  | S : pre:nat -> nat

(* First, this inductive shouldn't be accepted by the _current_ check *)
(* Second, this inductive shouldn't be accepted by _any_ check *)
type p : nat -> Type =
  | PSO : f:(p O -> Tot (p (S O))) -> p (S O)
  | POd : h:(p (S O)) -> p O

val bad : p (S O) -> Tot (p (S O))
let bad h = (PSO.f h) (POd h)

val loop : p (S O)
let loop = bad (PSO (fun h -> bad (POd.h h)))

(* looooop ....

   bad (PSO (bad (POd.h h))) ->                               (unfold+project)
   (fun h -> POd.h h) (POd (PSO (fun h -> POd.h h))) ->       (beta+project)
   bad (PSO (bad (POd.h h)))

 *)
