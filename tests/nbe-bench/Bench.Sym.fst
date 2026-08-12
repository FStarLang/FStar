module Bench.Sym
(* Open/symbolic term: the result stays a big residual term.
   Call-by-name should be at an advantage here (it never builds closures
   for arguments it does not scrutinize), and readback dominates for NBE. *)
open FStar.Tactics.V2
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec mapf (#a #b:Type) (f:a -> b) (l:list a) : list b =
  match l with | [] -> [] | x::xs -> f x :: mapf f xs

let _ = assert True by (
  let steps = [delta; zeta; iota; primops] in
  let t = quote (fun (g:int -> int) -> mapf g (upto 60)) in
  let _ = norm_term steps t in ())
