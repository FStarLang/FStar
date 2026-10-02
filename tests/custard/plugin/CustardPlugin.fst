module CustardPlugin

(* Section 12.8: a plugin compiled by Custard, loaded into a compiler
   compiled by Custard.  The two runs share nothing but the .cui that the
   compiler's own build wrote, so every type this file mentions across the
   boundary -- Prims.int, string, and the embedding machinery the [plugin]
   attribute generates -- has to be laid out the same way on both sides.

   [g] is [irreducible] on purpose: it is what makes CustardPluginTest a
   real test rather than an accident.  Without the plugin loaded, no
   normalizer can unfold it and the tactic fails; with it, the native step
   answers. *)

[@@plugin]
type t =
  | A of int
  | B of int & bool
  | C : int -> string -> t

[@@plugin]
irreducible
let f (x:int) : int = x + 123

[@@plugin]
irreducible
let flip (x:t) : t =
  match x with
  | A x -> C x ""
  | B (i, b) -> B (-i, not b)
  | C x _ -> A x

[@@plugin]
type record = { a : int; b : bool }

[@@plugin]
irreducible
let fr (x : record) : record =
  if x.b then { x with a = -x.a } else { x with b = true }

(* Section 13.4: plugins polymorphic in a type.  Nothing can be done to a
   value whose type is unknown, so the embedding for [a] is the identity on
   the syntax the caller passed; the type arguments themselves arrive as
   ordinary arguments and the generated interpretation drops them. *)

[@@plugin]
irreducible
let pid (#a:Type) (x:a) : a = x

[@@plugin]
irreducible
let psnd (#a:Type) (#b:Type) (x:a) (y:b) : b = y

[@@plugin]
irreducible
let pcount (#a:Type) (x:a) (n:int) : int = n + 7

[@@plugin]
irreducible
let pswap (#a:Type) (#b:Type) (x:a) (y:b) : b & a = (y, x)

(* Tactic plugins whose bodies use [&&]/[||] with a Tac operand.  Phase 1
   elaborates such a connective into an [if] (and, for an impure left operand,
   a [let]); that elaboration must carry the same effect annotations phase 2
   would have given it, since with --ext phase2_core it is the term that is
   extracted.  Without them the ML code applied a pure [if] to the proof state
   and called [is_unit] without one, and the plugin did not compile -- which
   is how this first showed up, in Pulse.Checker.Return.check_core. *)

let is_unit (t:FStar.Tactics.V2.term) : FStar.Tactics.V2.Tac bool =
  FStar.Reflection.TermEq.Simple.term_eq t (`unit)

[@@plugin]
irreducible
let sc_right (b c:bool) (t:FStar.Tactics.V2.term) : FStar.Tactics.V2.Tac bool =
  b || (not c && not (is_unit t))

[@@plugin]
irreducible
let sc_left (t:FStar.Tactics.V2.term) (b:bool) : FStar.Tactics.V2.Tac bool =
  is_unit t && not b
