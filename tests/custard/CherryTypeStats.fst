module CherryTypeStats
open FStar.All

(* --custard_type_stats: a nested unboxed record counts all of its fields, a
   variant its largest constructor plus a tag word, and a boxed type one
   reference, with its cell's counts alongside. *)

type pt = { x: int; y: int }
type seg = { a: pt; b: pt; label: string }
type shape = | Dot of int | Seg of seg | Empty

[@@FStar.Attributes.cherry_boxed]
type big = { s: seg; n: int }

let len (s:seg) : int = s.b.x - s.a.x + s.b.y - s.a.y

let size (h:shape) : int =
  match h with
  | Dot _ -> 0
  | Seg s -> len s
  | Empty -> 0

let weight (g:big) : int = len g.s + g.n

let main () : ML unit =
  let p0 : pt = { x = 0; y = 0 } in
  let p1 : pt = { x = 3; y = 4 } in
  let sg : seg = { a = p0; b = p1; label = "s" } in
  let g : big = { s = sg; n = 1 } in
  FStar.IO.print_string (string_of_int (size (Seg sg) + weight g) ^ "\n")
