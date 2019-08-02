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
module FStar.Algebra.CommMonoid

open FStar.Mul

unopteq
type cm (a:Type) =
  | CM :
    unit:a ->
    mult:(a -> a -> a) ->
    identity : (x:a -> Lemma (unit `mult` x == x)) ->
    associativity : (x:a -> y:a -> z:a ->
                      Lemma (x `mult` y `mult` z == x `mult` (y `mult` z))) ->
    commutativity:(x:a -> y:a -> Lemma (x `mult` y == y `mult` x)) ->
    cm a

let right_identity (#a:Type) (m:cm a) (x:a) :
    Lemma (CM?.mult m x (CM?.unit m) == x) =
  CM?.commutativity m x (CM?.unit m); CM?.identity m x

let int_plus_cm : cm int =
  CM 0 (+) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())

let int_multiply_cm : cm int =
  CM 1 ( * ) (fun x -> ()) (fun x y z -> ()) (fun x y -> ())
