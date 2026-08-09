module SepLib
(* Section 12: the upstream unit of the separate-compilation test.  Nothing
   here refers to SepApp; the point is that it is compiled once, on its own,
   and SepApp reuses the result instead of compiling any of it again. *)
open FStar.List.Tot

type shape =
  | Circle : nat -> shape
  | Rect   : nat -> nat -> shape

(* A one-field type, which the layout analysis collapses to its payload.  The
   importer must adopt that verdict rather than reach its own. *)
type tag = { untag : int }

let area (s:shape) : int =
  match s with
  | Circle r  -> 3 * r * r
  | Rect w h  -> w * h

let sum_areas (l:list shape) : int = fold_left (fun acc s -> acc + area s) 0 l

let bump (t:tag) : tag = { untag = t.untag + 1 }
