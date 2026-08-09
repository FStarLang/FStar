module Nonempty

(* A top-level definition whose effect is not Tot/GTot has its effect
   masked, so its type must be shown to be inhabited; otherwise a
   divergent term could be used to inhabit any type, including False.
   See issue #4401. These tests pin down the resulting error message. *)

open FStar.All

assume val diverge (#a: Type) (_: unit) : Dv a

(* The motivating unsoundness: without the obligation this was accepted
   with only a warning. *)
[@@expect_failure [19]]
let bad : False = diverge ()

(* The type need not be empty for the check to fail; it only has to be
   one that F* cannot see is inhabited. *)
[@@expect_failure [19]]
let bad_refinement : (x: int{x > 0 /\ x < 0}) = diverge ()

noeq
type record = { fst: int; snd: bool }

[@@expect_failure [19]]
let bad_record : record = diverge ()

(* Effects other than Div are checked too. *)
assume val raise_it (#a: Type) (_: unit) : ML a

[@@expect_failure [19]]
let bad_ml : False = raise_it ()

(* Types the normalizer can see are inhabited need no annotation. *)
let ok_int : int = diverge ()
let ok_bool : bool = diverge ()
let ok_string : string = diverge ()
let ok_fun : int -> string = diverge ()

(* Everything else is discharged by supplying a witness. *)
let _ : nonempty record = nonempty_intro ({ fst = 0; snd = false })
let ok_record : record = diverge ()
