module Deriving

(* Section 130.  [@@PpxDerivingYoJson] must reach the generated OCaml as the
   ppx item attribute [[@@deriving yojson]] on the type it decorates, and on
   no other type.

   Extraction only: what the attribute asks for is a preprocessor's work, and
   running it would make this test a test of ppx_deriving_yojson.  What is
   Custard's is which declarations carry the attribute and which do not. *)

[@@FStar.Attributes.PpxDerivingYoJson]
type color =
  | Red
  | Green
  | Blue

[@@FStar.Attributes.PpxDerivingYoJson]
noeq
type point = { px : Prims.int; py : Prims.int }

(* No attribute, and two fields so that the newtype collapse of section 5.2
   leaves it a record: nothing may be derived for it. *)
noeq
type span = { lo : Prims.int; hi : Prims.int }

let pick (c:color) : Prims.int =
  match c with
  | Red -> 0
  | Green -> 1
  | Blue -> 2

let shift (p:point) : point = { p with px = p.px + 1 }

let widen (s:span) : span = { s with hi = s.hi + 1 }
