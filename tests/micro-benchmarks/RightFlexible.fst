module RightFlexible

(* Misc checks that we allow a trailing comma or semicolon
   in the syntax. *)

open FStar.Tactics
open Prims { string, int, }

(* Parses, but fails *)
[@@expect_failure]
%splice[a;b;] (fail "")

type r = { x:int; y:int; }

let foo (v:r) : r = {
  x = v.y;
  y = v.x;
}

let foo2 (v:r) =
  match v with
  | { x = x; y = y; } -> { x = y; y = x; }

let l1 : list int = [1;2;3;4;]

let _ =
  match l1 with
  | [1;2;3;4;] -> ()

[@@ "attr1"; "attr2"; ]
let x : unit = ()
