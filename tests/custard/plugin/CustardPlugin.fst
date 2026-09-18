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
