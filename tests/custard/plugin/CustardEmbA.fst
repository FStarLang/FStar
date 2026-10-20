module CustardEmbA

(* Issue #4689, section 13.7.  The upstream unit: a [@@plugin] inductive,
   whose embedding this unit generates and exports.  See the Makefile. *)

[@@plugin]
type color =
  | Red
  | Green
  | Blue of int

[@@plugin]
irreducible
let next (c:color) : color =
  match c with
  | Red -> Green
  | Green -> Blue 0
  | Blue n -> Blue (n + 1)
