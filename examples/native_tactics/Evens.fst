module Evens
type unary_nat =
| U0 : unary_nat
| US : unary_nat -> unary_nat

type even : unary_nat -> Type =
| Even0 : even U0
| Even_SSn : n: unary_nat -> even n -> even (US (US n))

[@plugin]
let rec nat2unary (n: nat) : unary_nat = 
  if n = 0 then U0  else US (nat2unary (n - 1))

open FStar.Tactics

let even0 () : Lemma (even U0) = ()
let evenSSn (n: unary_nat) : 
  Lemma (requires even n)
        (ensures even (US (US n))) =
 // What's the proper way to do this?
 assert_by_tactic (even n ==> even (US (US n)))
                  (fun () -> ignore (implies_intro ());
                          squash_intro ();
                          apply (`Even_SSn);
                          assumption ())
[@plugin]
let prove_even () : Tac unit =
   ignore (repeat (fun () -> apply_lemma (`evenSSn)));
   apply_lemma (`even0)
