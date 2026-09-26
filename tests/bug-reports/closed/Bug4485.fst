module Bug4485

(* FStarLang/FStar#4485: the VC simplifier's [clearly_inhabited] judged an
   arrow type inhabited from its result type alone, ignoring the
   computation's postcondition, and so rewrote [nonempty e] and
   [exists (g:e). True] to [True] for the empty type [e] below, proving
   [False]. Since #4515, a computation type has only a result type, and the
   postcondition is a refinement of it, which [clearly_inhabited] does not
   consider inhabited. *)

open FStar.Classical

type e = unit -> Pure int (requires True) (ensures (fun r -> False))

(* [e] is empty: a witness yields [False]. *)
let witness_gives_false (g:e) : Lemma False = let _ = g () in ()

[@@expect_failure [19]]
let bad_nonempty () : Lemma False =
  assert_norm (nonempty e);
  exists_elim False #e #nonempty_tag () (fun g -> let _ = g () in ())

[@@expect_failure [19]]
let bad_exists () : Lemma False =
  assert_norm (exists (g:e). True);
  exists_elim False #e #(fun _ -> True) () (fun g -> let _ = g () in ())

type e_bool = unit -> Pure bool (requires True) (ensures (fun r -> False))

[@@expect_failure [19]]
let bad_bool () : Lemma False =
  assert_norm (exists (g:e_bool). True);
  exists_elim False #e_bool #(fun _ -> True) () (fun g -> let _ = g () in ())

(* Controls from the issue: [False] follows neither from an inhabited arrow
   type, nor from an empty one given by a refinement of its result type, nor
   from one that is inhabited only vacuously. *)
type ok = unit -> Pure int (requires True) (ensures (fun r -> True))

[@@expect_failure [19]]
let bad_ok () : Lemma False =
  assert_norm (exists (g:ok). True);
  exists_elim False #ok #(fun _ -> True) () (fun g -> let _ = g () in ())

type e_refine = unit -> Tot (r:int{False})

[@@expect_failure [19]]
let bad_refine () : Lemma False =
  assert_norm (exists (g:e_refine). True);
  exists_elim False #e_refine #(fun _ -> True) () (fun g -> let _ = g () in ())

type vacuous = unit -> Pure int (requires False) (ensures (fun r -> False))

let vacuous_witness : vacuous = fun () -> false_elim ()

[@@expect_failure [19]]
let bad_vacuous (g:vacuous) : Lemma False = let _ = g () in ()
