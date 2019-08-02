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
module Bijection

(* Definition of the bijection properties *)
type injection (#a:Type) (#b:Type) (f:a -> Tot b) = 
  (forall (x:a) (y:a). f x == f y ==> x == y)
  (* (forall (x:a) (y:a).{:pattern (f x);(f y)} f x == f y ==> x == y) *)
  (* CH: this pattern seems dangerous (used to have parenthesis around
         "(f x);(f y)", but that caused warning -- probably not parsed well)*)

irreducible type trigger (#a: Type) (x:a) = True
type surjection (#a:Type)(#b:Type) (f:a -> Tot b) = 
  (forall (y:b). {:pattern (trigger y)} (exists (x:a). f x == y))
type bijection (#a:Type) (#b:Type) (f:a -> Tot b) = 
  injection f /\ surjection f
type bij (#a:Type) (#b:Type) = f:(a -> Tot b){bijection f}

(* giving the inverse function is the best way to prove that a function is a
   bijection *)
type inverses (#a:Type) (#b:Type) (f:a -> Tot b) (g:b -> Tot a) =
   (forall (y:b). f (g y) == y) /\
   (forall (x:a). g (f x) == x)
val lemma_inverses_bij: #a:Type -> #b:Type -> f:(a -> Tot b) 
  -> g:(b -> Tot a) 
  -> Lemma (requires (inverses f g))
           (ensures (bijection f))
let lemma_inverses_bij #a #b f g = ()
