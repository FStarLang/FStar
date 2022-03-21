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
module FStar.Monotonic.Witnessed

open FStar.Preorder

(* 
   A module that defines the 'witnessed' logical capability/modality
   that is the basis of reasoning about monotonic state in F*, as
   discussed in Ahman et al.'s POPL 2018 paper "Recalling a Witness:
   Foundations and Applications of Monotonic State". Compared to the 
   POPL paper, where 'witnessed' and 'witnessed_weakening' were 
   simply postulated as axioms, this module defines them on top of 
   a more basic hybrid modal extension of F*'s reasoning logic (see 
   the corresponding fst file). Also, compared to the POPL paper, this 
   module proves many additional logical properties of 'witnessed'.
*)

(* Witnessed modality *)

[@@ remove_unused_type_parameters [0; 1; 2]]
val witnessed : #state:Type -> rel:preorder state -> p:(state -> Type0) -> Type0

(* Weakening for the witnessed modality *)

val lemma_witnessed_weakening :#state:Type
                               -> rel:preorder state
                               -> p:(state -> Type0)
                               -> q:(state -> Type0)
                               -> Lemma (requires (forall s. p s ==> q s))
                                       (ensures  (witnessed rel p ==> witnessed rel q))

(* Some logical properties of the witnessed modality *)

val lemma_witnessed_constant :#state:Type
                              -> rel:preorder state
                              -> p:Type0
                              -> Lemma (witnessed rel (fun _ -> p) <==> p)

val lemma_witnessed_nested :#state:Type
                            -> rel:preorder state
                            -> p:(state -> Type0)
                            -> Lemma (witnessed rel (fun _ -> witnessed rel p) <==> witnessed rel p)

val lemma_witnessed_and :#state:Type
                         -> rel:preorder state
                         -> p:(state -> Type0) 
                         -> q:(state -> Type0)
                         -> Lemma (witnessed rel (fun s -> p s /\ q s) <==> (witnessed rel p /\ witnessed rel q))

val lemma_witnessed_or :#state:Type
                        -> rel:preorder state
                        -> p:(state -> Type0)
                        -> q:(state -> Type0)
                        -> Lemma ((witnessed rel p \/ witnessed rel q) ==> witnessed rel (fun s -> p s \/ q s))

val lemma_witnessed_impl :#state:Type
                          -> rel:preorder state
                          -> p:(state -> Type0)
                          -> q:(state -> Type0)
                          -> Lemma ((witnessed rel (fun s -> p s ==> q s) /\ witnessed rel p) ==> witnessed rel q)

val lemma_witnessed_forall :#state:Type
                            -> #t:Type
                            -> rel:preorder state
                            -> p:(t -> state -> Type0) 
                            -> Lemma ((witnessed rel (fun s -> forall x. p x s)) <==> (forall x. witnessed rel (p x)))

val lemma_witnessed_exists :#state:Type
                            -> #t:Type
                            -> rel:preorder state
                            -> p:(t -> state -> Type0) 
                            -> Lemma ((exists x. witnessed rel (p x)) ==> witnessed rel (fun s -> exists x. p x s))
