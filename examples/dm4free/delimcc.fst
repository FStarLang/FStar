(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
let kont a = f:cont a{forall k1 k2.{:pattern (f k1); (f k2)} feq k1 k2 ==> f k1 == f k2}

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
let kont2 (result:Type) a = f:cont2 result a{forall k1 k2.{:pattern (f k1); (f k2)} feq k1 k2 ==> f k1 == f k2}

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


(* Version without any refinements *)

let cont3 (a:Type) = (a -> Tot result) -> Tot result

unfold let return_k3 (#a:Type) (x:a) : cont3 a =
        fun k -> k x

unfold let bind_k3 (#a:Type) (#b:Type)
                (m:cont3 a) (f:a -> Tot (cont3 b)) : cont3 b =
        fun k -> m (fun x -> f x k)

(* Don't know why this is not automatic in lu. *)
val ext : #a:Type -> #b:Type ->
         p:(a -> Tot b) ->
         Lemma ( (fun x -> p x) == p )
let ext #a #b (p : a -> Tot b) = ()

val left_unit3 : #a:Type -> #b:Type ->
                 x:a -> f:(a -> Tot (cont3 b)) ->
                 Lemma (bind_k3 (return_k3 x) f == f x)
let left_unit3 #a #b x f = ext (f x)

val right_unit3 : #a:Type ->
                  m:(cont3 a) ->
                  Lemma (bind_k3 m return_k3 == m)
let right_unit3 #a m = ()

val associativity3 : #a:Type -> #b:Type -> #c:Type ->
                     m:(cont3 a) ->
                     f:(a -> Tot (cont3 b)) ->
                     g:(b -> Tot (cont3 c)) ->
                     Lemma (bind_k3 (bind_k3 m f) g ==
                            bind_k3 m (fun x -> bind_k3 (f x) g))
let associativity3 #a #b #c m f g = ()

val callcc3 : #a:Type -> #b:Type ->
              ((a -> Tot (cont3 b)) -> Tot (cont3 a)) ->
              Tot (cont3 a)
let callcc3 #a #b f = fun k -> f (fun x _ -> k x) k

val shift3 : #a:Type ->
             ((a -> Tot (cont3 result)) -> Tot (cont3 result)) ->
             Tot (cont a)
let shift3 #a h = fun c -> h (fun v c' -> c' (c v)) (fun x -> x)

val reset3 : (unit -> Tot (cont result)) -> Tot (cont result)
let reset3 m = fun c -> c (m () (fun x -> x))
