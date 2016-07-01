module IFC

(********************************************************************************)
(* Effect (ifc a) : A monad for dynamic information-flow control                *)
(********************************************************************************)
type label =
  | Low
  | High

let join l1 l2 = match l1, l2 with 
  | _, High
  | High, _ -> High
  | _ -> Low

type err (a:Type) =
  | Leak 
  | Result : v:a -> err a
open FStar.FunctionalExtensionality

let ifc (a:Type) = l0:label  //sensitivity of data seen so far, analogous to the PC label
		 -> Tot (err (a 
			     * l1:label{join l0 l1 = l1} //sensitivity of data computed by this computation, at least as much as what was seen so far; Need this invariant to prove the monad laws
			     )
		       )
let eq_ifc (a:Type) (f:ifc a) (g:ifc a) = 
   forall l. f l == g l

let return_ifc (a:Type) (x:a) : ifc a = fun l -> Result (x, l)
let bind_ifc (a:Type) (b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b 
  = fun l0 -> match f l0 with 
	   | Leak -> Leak
	   | Result (x, l1) -> 
	     match g x l1 with
	     | Leak -> Leak
	     | Result (y, l2) -> Result(y, join l1 l2)

val left_unit: a:Type -> b:Type -> x:a -> f:(a -> Tot (ifc b)) 
	    -> Lemma (eq_ifc b (bind_ifc a b (return_ifc a x) f) (f x))
let left_unit a b x f = ()

val right_unit: a:Type -> f:ifc a -> Lemma (eq_ifc a (bind_ifc a a f (return_ifc a)) f)
let right_unit a f = ()

val associativity: a:Type -> b:Type -> c:Type -> f:ifc a -> g:(a -> Tot (ifc b)) -> h:(b -> Tot (ifc c))
		 -> Lemma (eq_ifc c (bind_ifc a c f (fun x -> bind_ifc b c (g x) h)) (bind_ifc b c (bind_ifc a b f g) h))
let associativity a b c f g h = ()		 

//Some dummy implementations of actions for illustration purposes
//Probably better to just take them axiomatically
let read_low () : ifc nat = fun l -> Result (0, l)
let read_high () : ifc nat = fun l -> Result (42, High)
let write_low () : ifc unit = fun l -> 
  match l with 
  | High -> Leak
  | _ -> Result((), l)
let write_high () : ifc unit = fun l -> Result ((), l)
  
