module Bench.Sym
(* Open/symbolic term: the argument [g] is a bound variable, so reduction
   cannot compute the result away and the normal form stays a large residual
   term -- 20000 applications of [g], each under a beta-reduced lambda.

   This is the regime where call-by-name is expected to do well: it never
   builds a closure for an argument it does not scrutinise, whereas NBE has
   to evaluate into the semantic domain and then read the whole residual
   back into syntax.

   Note this is a *norm request* under a binder, not a tactic call, so it is
   driven by --use_nbe like every other module here. Bench.SymTac* measure
   the tactic norm_term path separately. *)

let rec upto (n:nat) : list int = if n = 0 then [] else n :: upto (n-1)
let rec mapf (#a #b:Type) (f:a -> b) (l:list a) : list b =
  match l with | [] -> [] | x::xs -> f x :: mapf f xs

#push-options "--no_smt"
let opn (g:int -> int) : list int =
  FStar.Pervasives.norm [delta; zeta; iota; primops] (mapf (fun x -> g (x + 1)) (upto 20000))
#pop-options
