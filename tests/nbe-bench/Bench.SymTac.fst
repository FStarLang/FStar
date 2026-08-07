module Bench.SymTac
(* Tactic-level norm_term on an open term.

   Tactic norm_term calls Normalize.normalize directly and so is NOT affected
   by --use_nbe; the engine has to be chosen with the explicit [nbe] step.
   That is why this is three modules instead of one flag flip:
   Bench.SymTac uses the normalizer, Bench.SymTacNbe uses NBE, and
   Bench.SymTacBase does the identical quotation without normalizing and is
   the baseline to subtract.

   `open FStar.Tactics.V2` alone costs ~15s of module loading, so the
   normalized term has to be large or the difference is lost in the noise of
   that baseline. *)
open FStar.Tactics.V2
let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec mapf (#a #b:Type) (f:a -> b) (l:list a) : list b =
  match l with | [] -> [] | x::xs -> f x :: mapf f xs

let _ = assert True by (
  let steps = [delta; zeta; iota; primops] in
  let t = quote (fun (g:int -> int) -> mapf (fun x -> g (x + 1)) (upto 20000)) in
  let _ = norm_term steps t in ())
