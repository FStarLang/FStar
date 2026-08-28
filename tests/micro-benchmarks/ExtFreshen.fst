module ExtFreshen

(* A test for `--ext freshen`, which restarts the solver before every
   top-level declaration. The option is passed by the Makefile, so that the
   same file can also be checked with the option off.

   The point of this test is not just that the option is accepted, but that
   the SMT context is correctly replayed after each restart: every
   declaration below depends on facts (definitions, lemmas, axioms) that were
   introduced by the ones before it, so a restart that loses the context
   would make them fail. *)

let rec fact (n:nat) : nat =  if n = 0 then 1 else n * fact (n - 1)

let rec fact_pos (n:nat) : Lemma (ensures fact n > 0) =
  if n = 0 then () else fact_pos (n - 1)

let fact_5 () : Lemma (fact 5 == 120) = ()

assume val p : int -> prop
assume val p_zero : squash (p 0)
assume val p_succ (n:int) : Lemma (requires p n) (ensures p (n + 1))

let p_two () : Lemma (p 2) =
  p_succ 0;
  p_succ 1

type color = | Red | Green | Blue

let is_red (c:color) : bool = Red? c

let red_is_red () : Lemma (is_red Red /\ ~(is_red Green)) = ()

let fact_pos_still_available (n:nat) : Lemma (fact n <> 0) =
  fact_pos n
