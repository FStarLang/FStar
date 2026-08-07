module Bench.SymNbe
(* Same as Bench.Sym but with the explicit [nbe] norm step. Tactic-level
   norm_term calls [normalize] directly, so they are NOT affected by
   --use_nbe; the engine must be selected with the [nbe] step. *)
open FStar.Tactics.V2
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec mapf (#a #b:Type) (f:a -> b) (l:list a) : list b =
  match l with | [] -> [] | x::xs -> f x :: mapf f xs

let _ = assert True by (
  let steps = [nbe; delta; zeta; iota; primops] in
  let t = quote (fun (g:int -> int) -> mapf g (upto 60)) in
  let _ = norm_term steps t in ())
