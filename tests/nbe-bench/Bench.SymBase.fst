module Bench.SymBase
(* Baseline for Bench.Sym / Bench.SymNbe: same quotation, no normalization. *)
open FStar.Tactics.V2
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec mapf (#a #b:Type) (f:a -> b) (l:list a) : list b =
  match l with | [] -> [] | x::xs -> f x :: mapf f xs
let _ = assert True by (
  let t = quote (fun (g:int -> int) -> mapf g (upto 60)) in
  let _ = t in ())
