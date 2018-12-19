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
module FStar.Preorder

(* Preordered relations and stable predicates *)

type relation (a:Type) = a -> a -> Type0

type predicate (a:Type) = a -> Type0

let reflexive (#a:Type) (rel:relation a) =
  forall (x:a). rel x x

let transitive (#a:Type) (rel:relation a) =
  forall (x:a) (y:a) (z:a). (rel x y /\ rel y z) ==> rel x z

let preorder_rel (#a:Type) (rel:relation a) =
  reflexive rel /\ transitive rel

type preorder (a:Type) = rel:relation a{preorder_rel rel}

let stable (#a:Type) (p:predicate a) (rel:relation a{preorder_rel rel}) =
  forall (x:a) (y:a). (p x /\ rel x y) ==> p y
