module Bug1601

(*
 * This proof of False was reported by @joonwonc
 * It has been fixed by adding typing guards to the equational axioms for recursive functions
 *)

let rec log (n:nat{n > 0}) :nat = if n = 0 then 1 + log n else 1  //without the typing guards, the definition of log is not well-founded

let bar (n:nat) = True

val foo : nat -> Type0
let foo j = let _ = () in j == 0 \/ bar (log j)  //force a deep embedding of foo

[@expect_failure [19]]
let test (j:nat) : unit =
  assert (foo j);
  assert (j > 0)  //this would succeed earlier, effectively proving (forall (j:nat). j > 0), and hence False
