(* Based on 
     Philip Wadler's 
       Monads and Composable Continuations
       Lisp and Symbolic Computation
       1993
*)       
module DelimCC
open FStar.FunctionalExtensionality

assume type result : Type0
type cont (a:Type) = (a -> Tot result) -> Tot result
let kont a = f:cont a{forall k1 k2.{:pattern (f k1); (f k2)} feq k1 k2 ==> f k1 = f k2}

val return_k: a:Type -> x:a -> Tot (cont a)
let return_k a x = fun k -> k x
  
val bind_k: a:Type -> b:Type -> cont a -> (a -> Tot (cont b)) -> Tot (cont b)
let bind_k a b f g k = f (fun x -> g x k)

val right_unit: a:Type -> f:kont a -> Lemma (feq (bind_k a a f (return_k a)) f)
let right_unit a f = ()

val left_unit: a:Type -> b:Type -> x:a -> f:(a -> Tot (kont b)) 
	    -> Lemma (feq (bind_k a b (return_k a x) f) (f x))
let left_unit a b x f = ()

val associativity: a:Type -> b:Type -> c:Type -> f:kont a -> g:(a -> Tot (kont b)) -> h:(b -> Tot (kont c))
		 -> Lemma (feq (bind_k a c f (fun x -> bind_k b c (g x) h)) (bind_k b c (bind_k a b f g) h))
let associativity a b c f g h = ()		 
  
val callcc : a:Type -> b:Type
	   -> ((a -> Tot (cont b)) -> Tot (cont a))
	   -> Tot (cont a)
let callcc a b f = fun k -> f (fun x _ -> k x) k

val shift: a:Type -> ((a -> Tot (cont result)) -> Tot (cont result)) -> Tot (cont a)
let shift a h = fun c -> h (fun v c' -> c' (c v)) (fun x -> x)

val reset: (unit -> Tot (cont result)) -> Tot (cont result)
let reset m = fun c -> c (m () (fun x -> x))


////////////////////////////////////////////////////////////////////////////////
//Take 2: Murthy types
////////////////////////////////////////////////////////////////////////////////
type cont2 (result:Type) (a:Type) = (a -> Tot result) -> Tot result
let kont2 (result:Type) a = f:cont2 result a{forall k1 k2.{:pattern (f k1); (f k2)} feq k1 k2 ==> f k1 = f k2}

val return_k2: res:Type -> a:Type -> x:a -> Tot (cont2 res a)
let return_k2 res a x = fun k -> k x
  
val bind_k2: res:Type -> a:Type -> b:Type -> cont2 res a -> (a -> Tot (cont2 res b)) -> Tot (cont2 res b)
let bind_k2 res a b f g k = f (fun x -> g x k)

val right_unit2: res:Type -> a:Type -> f:kont2 res a -> Lemma (feq (bind_k2 res a a f (return_k2 res a)) f)
let right_unit2 res a f = ()

val left_unit2: res:Type -> a:Type -> b:Type -> x:a -> f:(a -> Tot (kont2 res b)) 
	    -> Lemma (feq (bind_k2 res a b (return_k2 res a x) f) (f x))
let left_unit2 res a b x f = ()

val associativity2: res:Type -> a:Type -> b:Type -> c:Type -> f:kont2 res a -> g:(a -> Tot (kont2 res b)) -> h:(b -> Tot (kont2 res c))
		 -> Lemma (feq (bind_k2 res a c f (fun x -> bind_k2 res b c (g x) h)) (bind_k2 res b c (bind_k2 res a b f g) h))
let associativity2 res a b c f g h = ()		 
  
val callcc2 : res:Type -> a:Type -> b:Type
	   -> ((a -> Tot (cont2 res b)) -> Tot (cont2 res a))
	   -> Tot (cont2 res a)
let callcc2 res a b f = fun k -> f (fun x _ -> k x) k

val shift2: o:Type -> p:Type -> a:Type -> ((a -> Tot (cont2 o p)) -> Tot (cont2 p p)) -> Tot (cont2 p a)
let shift2 o p a h = fun c -> h (fun v c' -> c' (c v)) (fun x -> x)

val reset2: o:Type -> p:Type -> (unit -> Tot (cont2 p p)) -> Tot (cont2 o p)
let reset2 o p m = fun c -> c (m () (fun x -> x))
