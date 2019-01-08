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
module Preorder

(* Preordered relations and stable predicates *)

let relation (a:Type) = a -> a -> Type0

let predicate (a:Type) = a -> Type0

(* NB: It may be better to tag both of the next two definitions
       with the "inline" qualifier.

   This will cause the F* normalizer to produce Z3 proofs obligations
   that have fewer higher-order quantifiers, which is typically better for Z3.
*)
type preorder (#a:Type) (rel:relation a) = 
  (forall x . rel x x) /\ (forall x y z . rel x y /\ rel y z ==> rel x z)

type stable (#a:Type) (rel:relation a{preorder rel}) (p:predicate a) =
  forall x y . p x /\ rel x y ==> p y

(* NB: consider using this instead for readability ...? *)
let preorder_t (a:Type) = rel:relation a{preorder rel}
