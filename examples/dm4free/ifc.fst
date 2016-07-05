module IFC

(********************************************************************************)
(* Effect (ifc a) : A monad for dynamic information-flow control                *)
(********************************************************************************)
type label =
  | Low
  | High

let join l1 l2 =
  match l1, l2 with
  | _   , High
  | High, _    -> High
  | _   , _    -> Low

let flows l1 l2 =
  match l1, l2 with
  | High, Low -> false
  | _   , _   -> true

type err (a:Type) =
  | Leak 
  | Result : v:a -> err a

let ifc (a:Type) = label -> Tot (err (a * label))

(* open FStar.FunctionalExtensionality *)

let eq_ifc (a:Type) (f:ifc a) (g:ifc a) =
   forall l. f l == g l

let return_ifc (a:Type) (x:a) : ifc a = fun l -> Result (x, l)
let bind_ifc (a:Type) (b:Type) (f:ifc a) (g: a -> Tot (ifc b)) : ifc b 
  = fun l0 -> match f l0 with 
	   | Leak -> Leak
	   | Result (x, l1) -> 
	     match g x l1 with
	     | Leak -> Leak
	     | Result (y, l2) -> Result(y, l2)

val left_unit: a:Type -> b:Type -> x:a -> f:(a -> Tot (ifc b)) 
	    -> Lemma (eq_ifc b (bind_ifc a b (return_ifc a x) f) (f x))
let left_unit a b x f = ()

val right_unit: a:Type -> f:ifc a -> Lemma (eq_ifc a (bind_ifc a a f (return_ifc a)) f)
let right_unit a f = ()

val associativity: a:Type -> b:Type -> c:Type -> f:ifc a -> g:(a -> Tot (ifc b)) -> h:(b -> Tot (ifc c))
		 -> Lemma (eq_ifc c (bind_ifc a c f (fun x -> bind_ifc b c (g x) h)) (bind_ifc b c (bind_ifc a b f g) h))
let associativity a b c f g h = ()		 

// Some dummy implementations of actions for illustration purposes
// Probably better to just take them axiomatically
let read (l:label) : ifc bool = fun l0 -> Result (true, join l0 l)
let write (l:label) (b:bool) : ifc unit =
  fun l0 -> if flows l0 l then (Result ((), l0)) else Leak

let xor (b1:bool) (b2:bool) : Tot bool = not (b1 = b2)

// A sample monadic program (normally would write this after
// elaboration, but whatever, can write this in DM too)
val p : unit -> Pure (ifc unit) (requires True) (ensures (fun r -> forall l. r l = Leak))
(* Weak type (works): unit -> Tot (ifc unit) *)
(* Alternative strong type (doesn't work), (Valid(ApplyTT@2 @0))
  unit -> Tot (label -> Pure (err (unit * label)) (requires True) (ensures (fun r -> r = Leak))) *)
let p () = bind_ifc _ _ (read Low)              (fun b1 ->
           bind_ifc _ _ (read Low)              (fun b2 ->
           bind_ifc _ _ (write Low (b1 && b2))  (fun _  ->
           bind_ifc _ _ (read High)             (fun b3 ->
           bind_ifc _ _ (write High (b1 || b3)) (fun _  ->
                        (write Low (xor b3 b3))  )))))
