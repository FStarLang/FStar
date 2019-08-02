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

(* NOT EXPOSED BY THE INTERFACE [start] *)

(* 
   A hybrid modal extension to F*'s classical reasoning logic:
     - extends F*'s logic with two hybrid modal operators (get, set)
     - extends F*'s logic with corresponding logical axioms, based
       on the Kripke semantics of these two hybrid modal operators:

         w |= get p   iff   w |= p w

         w |= set p w'   iff   w' |= p

    We do not expose these modal operators to the users directly.
    Instead we use them below to define the 'witnessed' modality 
    which is the basis of reasoning about monotonic state in F*, 
    as discussed in Ahman et al.'s POPL 2018 paper "Recalling a 
    Witness: Foundations and Applications of Monotonic State".
*)

(* Hybrid modal operators *)
assume private type get : #world:Type -> (world -> Type0) -> Type0
assume private type set : #world:Type -> Type0 -> world -> Type0

(* Weakening for the get operator *)
assume val get_weakening :#world:Type
                          -> p:(world -> Type0)
                          -> q:(world -> Type0)
                          -> Lemma (requires (forall w. p w ==> q w))
                                  (ensures  (get p ==> get q))
                                  [SMTPat (get p); SMTPat (get q)]

(* Interaction axioms between the get and set operators *)
assume val get_set_axiom :#world:Type
                          -> p:Type0
                          -> Lemma (get (set #world p) <==> p)
                                  [SMTPat (get (set #world p))]

assume val set_get_axiom :#world:Type
                          -> w:world
                          -> p:(world -> Type0)
                          -> Lemma (set (get p) w <==> set (p w) w)
                                  [SMTPat (set (get p) w)]

assume val set_set_axiom :#world:Type
                          -> w:world
                          -> w':world
                          -> p:Type0
                          -> Lemma (set (set p w') w <==> set p w')
                                  [SMTPat (set (set p w') w)]

(* Useful derivable get lemma *)

private val get_constant_lemma :world:Type
                                -> p:Type0
                                -> Lemma (get #world (fun _ -> p) <==> p)
let get_constant_lemma world p = get_set_axiom #world p

(* Get and set commute with (non-modal) logical connectives *)

private val get_true :world:Type
                      -> Lemma (get #world (fun _ -> True))
let get_true world = get_constant_lemma world True

assume private val set_true :#world:Type
                             -> w:world
                             -> Lemma (set True w)

private val get_false :world:Type
                       -> Lemma (requires (get #world (fun _ -> False)))
                               (ensures  (False))
let get_false world = get_constant_lemma world False

assume val set_false :#world:Type
                      -> w:world
                      -> Lemma (requires (set False w)) 
                              (ensures  (False))

private val get_and_1 :#world:Type
                       -> p:(world -> Type0)
                       -> q:(world -> Type0)
                       -> Lemma (requires (get (fun w -> p w /\ q w)))
                               (ensures  (get p /\ get q))
let get_and_1 #world p q = ()

assume private val set_and_1 :#world:Type
                              -> w:world    
                              -> p:Type0
                              -> q:Type0
                              -> Lemma (requires (set (p /\ q) w))
                                      (ensures  (set p w /\ set q w))

assume private val get_and_2 :#world:Type
                              -> p:(world -> Type0)
                              -> q:(world -> Type0)
                              -> Lemma (requires (get p /\ get q))
                                      (ensures  (get (fun w -> p w /\ q w)))


assume private val set_and_2 :#world:Type
                              -> w:world
                              -> p:Type0
                              -> q:Type0
                              -> Lemma (requires (set p w /\ set q w))
                                      (ensures  (set (p /\ q) w))

private val get_or_1 :#world:Type
                      -> p:(world -> Type0)
                      -> q:(world -> Type0)
                      -> Lemma (requires (get p \/ get q))
                              (ensures  (get (fun w -> p w \/ q w)))
let get_or_1 #world p q = ()

assume private val set_or_1 :#world:Type
                             -> w:world
                             -> p:Type0
                             -> q:Type0
                             -> Lemma (requires (set p w \/ set q w))
                                     (ensures  (set (p \/ q) w))

assume private val get_or_2 :#world:Type
                             -> p:(world -> Type0)
                             -> q:(world -> Type0)
                             -> Lemma (requires (get (fun w -> p w \/ q w)))
                                     (ensures  (get p \/ get q))

assume private val set_or_2 :#world:Type
                             -> w:world
                             -> p:Type0
                             -> q:Type0
                             -> Lemma (requires (set (p \/ q) w))
                                     (ensures  (set p w \/ set q w))

private val get_impl_1 :#world:Type
                        -> p:(world -> Type0)
                        -> q:(world -> Type0)
                        -> Lemma (requires (get (fun w -> p w ==> q w) /\ get p))
                                (ensures  (get q))
let get_impl_1 #world p q = 
  get_and_2 (fun w -> p w ==> q w) p; 
  get_weakening (fun w -> (p w ==> q w) /\ p w) q

assume private val set_impl_1 :#world:Type
                               -> w:world
                               -> p:Type0
                               -> q:Type0
                               -> Lemma (requires (set (p ==> q) w /\ set p w))
                                       (ensures  (set q w))

assume private val get_impl_2 :#world:Type
                               -> p:(world -> Type0)
                               -> q:(world -> Type0)
                               -> Lemma (requires (get p ==> get q))
                                       (ensures  (get (fun w -> p w ==> q w)))

assume private val set_impl_2 :#world:Type
                               -> w:world
                               -> p:Type0
                               -> q:Type0
                               -> Lemma (requires (set p w ==> set q w))
                                       (ensures  (set (p ==> q) w))

private val get_forall_1_aux :#world:Type
                              -> #t:Type
                              -> p:(t -> world -> Type0)
                              -> x:t
                              -> Lemma (requires (get (fun w -> forall x. p x w)))
                                      (ensures  (get (fun w -> p x w)))
let get_forall_1_aux #world #t p x = 
  get_weakening (fun w -> forall x. p x w) (fun w -> p x w)

private val get_forall_1 :#world:Type
                          -> #t:Type
                          -> p:(t -> world -> Type0)
                          -> Lemma (requires (get (fun w -> forall x. p x w)))
                                  (ensures  (forall x. get (fun w -> p x w)))
let get_forall_1 #world #t p = ()

assume private val set_forall_1 :#world:Type
                                 -> #t:Type
                                 -> w:world
                                 -> p:(t -> Type0)
                                 -> Lemma (requires (set (forall x. p x) w))
                                         (ensures  (forall x. set (p x) w))

assume private val get_forall_2 :#world:Type
                                 -> #t:Type
                                 -> p:(t -> world -> Type0)
                                 -> Lemma (requires (forall x. get (fun w -> p x w)))
                                         (ensures  (get (fun w -> forall x. p x w)))

assume private val set_forall_2 :#world:Type
                                 -> #t:Type
                                 -> w:world 
                                 -> p:(t -> Type0)
                                 -> Lemma (requires (forall x. set (p x) w))
                                         (ensures  (set (forall x. p x) w))

private val get_exists_1_aux :#world:Type
                              -> #t:Type
                              -> p:(t -> world -> Type0)
                              -> x:t
                              -> Lemma (requires (get (fun w -> p x w)))
                                      (ensures  (get (fun w -> exists x. p x w)))
let get_exists_1_aux #world #t p x = 
  get_weakening (fun w -> p x w) (fun w -> exists x . p x w)

private val get_exists_1 :#world:Type
                          -> #t:Type
                          -> p:(t -> world -> Type0)
                          -> Lemma (requires (exists x. get (fun w -> p x w)))
                                  (ensures  (get (fun w -> exists x. p x w)))
let get_exists_1 #world #t p = ()

assume private val set_exists_1 :#world:Type
                                 -> #t:Type
                                 -> w:world
                                 -> p:(t -> Type0)
                                 -> Lemma (requires (exists x. set (p x) w)) 
                                         (ensures  (set (exists x. p x) w))

assume private val get_exists_2 :#world:Type
                                 -> #t:Type
                                 -> p:(t -> world -> Type0)
                                 -> Lemma (requires (get (fun w -> exists x. p x w)))
                                         (ensures  (exists x. get (fun w -> p x w)))

assume private val set_exists_2 :#world:Type
                                 -> #t:Type
                                 -> w:world
                                 -> p:(t -> Type0)
                                 -> Lemma (requires (set (exists x. p x) w)) 
                                         (ensures  (exists x. set (p x) w))

private val get_eq :#world:Type
                    -> #t:Type
                    -> v:t
                    -> v':t
                    -> Lemma (get #world (fun _ -> v == v') <==> v == v')
let get_eq #world #t v v' = 
  get_constant_lemma world (v == v')

assume private val set_eq :#world:Type
                           -> #t:Type
                           -> w:world
                           -> v:t
                           -> v':t
                           -> Lemma (set (v == v') w <==> v == v')

(* NOT EXPOSED BY THE INTERFACE [end] *)


(* EXPOSED BY THE INTERFACE [start] *)

(* Witnessed modality *)

let witnessed #state rel p = get (fun s -> forall s'. rel s s' ==> p s')

(* Weakening for the witnessed modality *)

let lemma_witnessed_weakening #state rel p q = ()

(* Some logical properties of the witnessed modality *)

let lemma_witnessed_constant #state rel p = get_constant_lemma state p

let lemma_witnessed_nested #state rel p = ()

let lemma_witnessed_and #state rel p q =
  let aux () :Lemma (requires (witnessed rel p /\ witnessed rel q))
                    (ensures  (witnessed rel (fun s -> p s /\ q s)))
    = get_and_2 (fun s -> forall s'. rel s s' ==> p s') (fun s -> forall s'. rel s s' ==> q s')
  in
  FStar.Classical.move_requires aux ()

let lemma_witnessed_or #state rel p q = ()

let lemma_witnessed_impl #state rel p q = 
  let aux () :Lemma (requires ((witnessed rel (fun s -> p s ==> q s) /\ witnessed rel p)))
                    (ensures  (witnessed rel q))
    = get_and_2 (fun s -> forall s'. rel s s' ==> p s' ==> q s') (fun s -> forall s'. rel s s' ==> p s')
  in
  FStar.Classical.move_requires aux ()

let lemma_witnessed_forall #state #t rel p =
  let aux () :Lemma (requires (forall x. witnessed rel (fun s -> p x s)))
                    (ensures  (witnessed rel (fun s -> forall x. p x s)))
    = get_forall_2 #state #t (fun x s -> forall s'. rel s s' ==> p x s')
  in
  FStar.Classical.move_requires aux ()

let lemma_witnessed_exists #state #t rel p = ()

(* EXPOSED BY THE INTERFACE [end] *)


(* NOT EXPOSED BY THE INTERFACE [start] *)

(* An equivalent past-view of the witnessed modality *)

let witnessed_past (#state:Type) (rel:preorder state) (p:(state -> Type0)) = 
  get (fun s -> exists s'. rel s' s /\ (forall s''. rel s' s'' ==> p s''))

val witnessed_defs_equiv_1 :#state:Type
                            -> rel:preorder state
                            -> p:(state -> Type0)
                            -> Lemma (requires (witnessed #state rel p)) 
                                    (ensures  (witnessed #state rel p))
let witnessed_defs_equiv_1 #state rel p = ()

val witnessed_defs_equiv_2 :#state:Type
                            -> rel:preorder state
                            -> p:(state -> Type0)
                            -> Lemma (requires (witnessed #state rel p)) 
                                    (ensures  (witnessed #state rel p))
let witnessed_defs_equiv_2 #state rel p = 
  get_weakening #state (fun s -> exists s'. rel s' s /\ (forall s''. rel s' s'' ==> p s'')) 
                       (fun s -> forall s'. rel s s' ==> p s')

(* NOT EXPOSED BY THE INTERFACE [end] *)
