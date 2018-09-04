module Inlining

open FStar.Tactics.Typeclasses

(** Unfolding **)
(* We do not want overloading to get in the way of verification, here's a first
   attempt at how to unfold methods properly. There's logic in the typechecker
   to unfold everything marked with @tcnorm just after phase 1. *)

(* regular class *)
class inhab a = {
    elem : unit -> a;
}

(* mark with tcnorm. we need to write it as a match and not call the
 * projector since the projector won't unfold (but it could..., maybe
 * we need an UnfoldAttrFully?) *)
[@tcnorm]
let elem' #a [|d : inhab a|] =
    match d with
    | Mkinhab elem -> elem

(* regular instance *)
[@ tcnorm]
instance inhab_unit : inhab unit = { elem = fun () -> admit #unit () }

(* This will only succeed if the found instance is inlined, sa
 * can be seen from the failure if one uses --tcnorm false *)
let f (u:unit) =
  let t = elem' #unit () in
  assert (forall y. y == 1)

#push-options "--tcnorm false"

[@expect_failure]
let f_fail (u:unit) =
  let t = elem' #unit () in
  assert (forall y. y == 1)

#pop-options
