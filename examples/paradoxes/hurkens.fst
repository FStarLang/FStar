module Hurkens

(* Hurkens paradox
   https://coq.inria.fr/distrib/current/stdlib/Coq.Logic.Hurkens.html
   This was brought to our attention by Yannick Forster and Steven Schäfer,
   who contributed the code below.
*)

assume val p2b: p:Type -> Tot (b:bool{b = true <==> p})

type b2p : bool -> Type =                          
  | B2pI : b2p true

assume val p2p2 : a:Type -> a -> Tot (b2p(p2b a))               

type V = a : Type -> ((a-> Tot bool) -> a -> Tot bool) -> a -> Tot bool
type U = V -> Tot bool

val sb : V -> Tot V
let sb (z : V) = fun (a:Type) r (x : a) -> r (z a r) x              
                                                     
val le : i : (U -> Tot bool) -> x: U -> Tot bool                                                     
let le i x = x (fun (a : Type) r y -> i (fun (v : V)-> sb v a r y))

val wf : U
let wf (z : V) = let y : (U -> Tot bool) = z U le in p2b (x : U -> b2p (le y x) -> Tot (b2p (y x)))               

let omega =
(fun (i : U -> Tot bool) (y : (x1 : U -> b2p (le i x1) -> Tot (b2p (i x1)))) ->
 y wf
   (p2p2
      ( x2 : U ->
       b2p (le (fun (a : U) -> i (fun (v : V) -> sb v U le a)) x2) ->
       b2p (i (fun (v : V) -> sb v U le x2)))
      (fun (x3 : U) -> fun
         (h0 : b2p (le (fun (a : U) -> i (fun (v : V) -> sb v U le a)) x3)) ->
       y (fun (v : V) -> sb v U le x3) h0)))

(* Currently this causes a blow up:
   Unexpected error: Bound term variable not found: x3
 *)
