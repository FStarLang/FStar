module Pulse.VC

open Pulse.Syntax.Base
open Pulse.Typing
module T = FStar.Tactics.V2

let discharge (vc : vc_t) : T.Tac (either (list issue) (discharged vc)) =
  match vc with
  | Trivial -> Inr ()
  | EquivToken g t1 t2 ->
    match T.check_equiv (elab_env g) t1 t2 with
    | Some d, _ -> Inr d
    | None, iss -> Inl iss

let resolve #a #vc (w : with_vc vc a) : T.Tac (either (list issue) a) =
  match discharge vc with
  | Inl iss -> Inl iss
  | Inr d -> Inr (w d)

#set-options "--print_implicits --print_universes"

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
