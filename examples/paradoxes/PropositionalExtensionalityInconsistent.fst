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

module PropositionalExtensionalityInconsistent
(* Variations of propositional and predicate extensionality
   defined for all of Type0 or for the type of sub-singletons
   is inconsistent *)

(* PropositionalExtensionality for the whole of Type0 is inconsistent,
   quite obviously since Type0 doesn't only include propositions.

   Proof by Kenji Maillard (adapted) *)
let propExt_Type = forall (p1 p2:Type0). (p1 <==> p2) <==> p1==p2

let propExt_Type_inconsistent ()
  : Lemma (requires propExt_Type)
          (ensures False)
  = let int_is_inhabited (x:int) : Lemma (int <==> unit) = () in
    int_is_inhabited 42

(* Maybe somewhat more subtle, propositional extensionality for all
   sub-singletons is also inconsistent. *)
let sub_singleton = a:Type{forall (x y:a). x == y}
let propExt_sub_singleton = forall (p1 p2:sub_singleton). (p1 <==> p2) <==> p1==p2
let propExt_sub_singleton_inconsistent()
  : Lemma (requires propExt_sub_singleton)
          (ensures False)
  = () //SMT finds the proof automatically, by noticing, e.g., T == ()


(* predicate extensionality essentially implies propositional
   extensionality. So, defined over Type0 predicates or sub-singleton
   predicates, it is also inconsistent *)


(* Here's a proof for Type0 *)
let predicate (a:Type0) = a -> Tot Type0
let peq (#a:Type0) (p1 p2:predicate a) =
  forall x. p1 x <==> p2 x
let predExt_Type =
    a:Type
    -> p1:predicate a
    -> p2:predicate a
    -> Lemma (requires (peq p1 p2))
            (ensures (p1 == p2))
let predExt_Type_inconsistent (ax:predExt_Type)
  : Lemma False
  = let p1 : predicate int = fun n -> c_True in
    let p2 : predicate int = fun n -> unit in
    ax int p1 p2


(* Here's a proof for sub-singletons *)
let predicate_ss (a:Type0) = a -> Tot sub_singleton
let peq_ss (#a:Type0) (p1 p2:predicate_ss a) =
    forall x. p1 x <==> p2 x
let predExt_ss =
    a:Type
    -> p1:predicate_ss a
    -> p2:predicate_ss a
    -> Lemma (requires (peq_ss p1 p2))
            (ensures (p1 == p2))
let predExt_ss_inconsistent (ax:predExt_ss)
  : Lemma False
  = let p1 : predicate_ss int = fun n -> c_True in
    let p2 : predicate_ss int = fun n -> unit in
    ax int p1 p2
