(*
   A minimal FStar.Tactics.Effect for the simplified effect system.

   TAC's *specification* is, like every other effect, just a name: a
   computation `Tac a (requires p) (ensures q)` is checked by the uniform
   pre/postcondition rules of the type checker.

   The `effect { TAC with { ... } }` block below plays no role in
   typechecking.  It only gives TAC an executable meaning, used by
   reification: extraction and the tactic engine turn a `Tac a` computation
   into a `tac_repr a`, i.e. a function from a proofstate.
*)
module FStar.Tactics.Effect

open FStar.All

(* The tactic engine's mutable proofstate handle.  Left abstract here; the
   real compiler binds it to FStarC.Tactics.Types.proofstate ref. *)
assume new type ref_proofstate : Type0

(* The representation of a tactic: a possibly-divergent, exception-raising computation that
   reads and updates the proofstate. *)
inline_for_extraction
let tac_repr (a: Type) : Type = ref_proofstate -> ML a

inline_for_extraction
let tac_return (a: Type) (x: a) : tac_repr a =
  fun _ -> x

inline_for_extraction
let tac_bind (a: Type) (b: Type) (f: tac_repr a) (g: a -> tac_repr b) : tac_repr b =
  fun ps -> g (f ps) ps

reflectable effect { TAC with { repr = tac_repr; return = tac_return; bind = tac_bind } }

assume sub_effect PURE  ~> TAC
assume sub_effect GHOST ~> TAC
assume sub_effect DIV   ~> TAC

(* ALL is not pure/divergent, so its lift into TAC needs an explicit term. *)
let lift_all_tac (a: Type u#a) (f: unit -> ALL a) : tac_repr a =
  fun _ -> f ()

sub_effect ALL ~> TAC = lift_all_tac

effect Tac (a: Type) = TAC a

(* NOTE: effect abbreviations may not take extra parameters: everything
   after the result type in a computation type is parsed as the use-site
   (requires ...) / (ensures ...).  So the old `TacH a pre post` is written
   directly as `Tac a (requires pre) (ensures post)`. *)
