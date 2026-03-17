module Pulse.VC

open FStar.Ghost { erased }
open Pulse.Syntax.Base
open Pulse.Typing
module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
module PCP = Pulse.Checker.Pure

let discharge (vc : vc_t) : T.Tac (either (list issue) (discharged vc)) =
  match vc with
  | Trivial -> Inr ()
  | Equiv g t1 t2 -> (
    let t1' = PCP.norm_well_typed_term (elab_env g) [NormSteps.unascribe; primops; iota] t1 in
    let t2' = PCP.norm_well_typed_term (elab_env g) [NormSteps.unascribe; primops; iota] t2 in
    (* RT typing does not expose a way to prove these equal, but they are. *)
    let eq1 : erased (RT.equiv (elab_env g) t1  t1') = RU.magic () in
    let eq2 : erased (RT.equiv (elab_env g) t2  t2') = RU.magic () in
    match T.check_equiv (elab_env g) t1' t2' with
    | Some tok, _ ->
      let equiv () : GTot (RT.equiv (elab_env g) t1 t2) =
        (eq1 `RT.Rel_trans _ _ _ _ _`
            RT.Rel_eq_token (elab_env g) t1' t2' () `RT.Rel_trans _ _ _ _ _`
            RT.Rel_sym _ _ _ eq2)
      in
      Inr (Ghost.hide (equiv ()))
    | None, iss -> Inl iss
  )
  | WellTypedGhost g e t -> (
    match T.core_check_term (elab_env g) e t T.E_Ghost with
    | None, iss -> Inl iss
    | Some d, _ ->
      Inr (Ghost.hide <| RT.T_Token (elab_env g) e (T.E_Ghost, t) ())
  )

let resolve #a #vc (w : with_vc vc a) : T.Tac (either (list issue) a) =
  match discharge vc with
  | Inl iss -> Inl iss
  | Inr d -> Inr (w d)

let map_guarded
  (#a : Type u#aa)
  (#b : Type u#bb)
  (x : guarded u#aa a)
  (f : a -> T.Tac b)
: guarded b
=
  let Guarded vc foo = x in
  Guarded vc (fun tok -> f (foo tok))

let unguard #a (x : guarded a) : T.Tac (either (list issue) a) =
  let Guarded vc foo = x in
  resolve foo
