(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
(*
  This module provides
     1. A GHOST effect, to encapsulate irrelevant computations
     2. A ghost type, to abstract computationally irrelevant values
*)
module Ghost
total new_effect GHOST = PURE

sub_effect
  PURE ~> GHOST = fun (a:Type) (wp:PureWP a) -> wp

effect GTot (a:Type) = GHOST a (pure_null_wp a) (pure_null_wp a)
effect Ghost (a:Type) (pre:Type) (post:PurePost a) =
       GHOST a
           (fun (p:PurePost a) -> pre /\ (forall (x:a). post x ==> p x))
           (fun (p:PurePost a) -> forall (x:a). pre /\ post x ==> p x)

private type ghost (a:Type) = a
val reveal: #a:Type -> ghost a -> GTot a
let reveal x = x

val hide: #a:Type -> a -> GTot (ghost a)
let hide x = x

val lemma_hide_reveal: #a:Type
                   -> x:ghost a
                   -> Lemma (ensures (hide (reveal x) = x))
let lemma_hide_reveal x = ()

assume val as_ghost: #a:Type
          -> f:(unit -> Tot a)
          -> Pure (ghost a)
                  (requires True)
                  (ensures (fun x -> reveal x = f ()))
