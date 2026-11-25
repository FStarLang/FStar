module TacAnyArm
open FStar.Tactics.V2

(* A reified [Tac] match whose arms are closures over the proofstate.  When
   one arm was typed [any], the match took its type from the other arms --
   here the pure [fun ps -> ()] of the [()] arm -- so applying it to the
   proofstate was judged pure, and, its result being unused, deleted along
   with the [fail] in the [any] arm.  Pulse's checker lost the check that
   rejects a ghost application of a stateful function this way. *)

type tag = | A | B

let pos (n:int) : Tac bool = n > 0

(* The arms [fail "A"] and [()] differ only in their arrows' effects; this
   was [any] before FStarLang/FStar#4905 joined them. *)
let check (n:int) (c:tag) : Tac int =
  if not (pos n) then (match c with A -> fail "A" | B -> ());
  n

let t_of (b:bool) : Type0 = if b then unit else unit

[@@"opaque_to_smt"] irreducible
let side (b:bool) : Tac (t_of b) = if b then fail "side" else ()

(* The inner match is [any] because [t_of b] has no representation (so this
   file is run with --warn_error -367); the [else] arm is a pure closure
   returning [unit]. *)
let check_dep (n:int) (c:tag) (b:bool) : Tac int =
  let _ : t_of b =
    if not (pos n) then (match c with A -> side b | B -> side (not b); ()) else () in
  n
