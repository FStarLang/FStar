module SplitLo

(* The bottom of a three-layer program: Custard compiles this, the
   hand-written OCaml in SplitMid.ml calls into it, and SplitHi calls that.
   Section 12.9 -- with one output file the middle layer could not exist. *)

type color = | Red | Green

let flip (c:color) : color =
  match c with
  | Red -> Green
  | Green -> Red

let add_one (x:int) : int = x + 1
