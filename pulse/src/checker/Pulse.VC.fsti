module Pulse.VC

open FStar.Stubs.Reflection.Types
open Pulse.Typing
open FStar.Issue
module T = FStar.Tactics.Effect
module RT = FStar.Stubs.Tactics.Types.Reflection

(* Recall: pulse terms are F* terms *)

(* Types of possible verification conditions. *)
noeq
type vc_t =
  | Trivial
  | EquivToken : env -> term -> term -> vc_t

(* Evidence for a VC being discharged, according to the kind. *)
let discharged (vc : vc_t) : Type =
  match vc with
  | Trivial -> unit
  | EquivToken g t1 t2 -> RT.equiv_token (elab_env g) t1 t2

(* Discharge a VC, producing evidence for it. May fail. *)
val discharge (vc : vc_t) : T.Tac (either (list issue) (discharged vc))

type with_vc (vc : vc_t) (a:Type) =
  discharged vc -> T.Tac a

val resolve #a #vc (w : with_vc vc a) : T.Tac (either (list issue) a)

(* Guarded values, there only if a VC succeeds. *)
noeq
type guarded (a:Type u#aa) : Type u#aa =
  | Guarded : vc:_ -> with_vc vc a -> guarded a

(* Working under a guard. *)
val map_guarded
  (#a : Type u#aa)
  (#b : Type u#bb)
  (g : guarded a)
  (f : a -> T.Tac b)
  : T.Tac (guarded b)

(* Unguarding = discharging the VC and applying the continuation. *)
val unguard #a (g : guarded a) : T.Tac (either (list issue) a)
