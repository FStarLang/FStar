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

module FStar.FunctionalExtensionality

inline_for_extraction
let on_domain (a:Type) (#b:a -> Type) ([@@@strictly_positive] f:arrow a b)
  = fun (x:a) -> f x

let feq_on_domain (#a:Type) (#b:a -> Type) (f:arrow a b)
  = ()

let idempotence_on_domain #a #b f
  = assert_norm (on_domain a f == (on_domain a (on_domain a f)))

let quantifier_as_lemma (#a:Type) (#b: a -> Type)
                        (f:squash (forall (x:a). b x))
                        (x:a)
    : Lemma (b x)
    = ()

open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Tactics.Types
open FStar.Tactics.Effect
(* we're early enough in the module stack that we need to reimplement
   a few of the tactic helpers *)
noextract
let try_with (f : unit -> Tac 'a) (h : exn -> Tac 'a) : Tac 'a =
    match catch f with
    | Inl e -> h e
    | Inr x -> x

noextract
let l_to_r (t:term) : Tac unit =
  ctrl_rewrite BottomUp
    (fun  _ -> true, Continue)
    (fun _ ->
      try t_apply_lemma false true t
      with _ -> t_trefl false)

let extensionality_1 (a:Type)
                     (b: a -> Type)
                     (f g: arrow a b)
                     (sq_feq : squash (feq f g))
  : Lemma (ensures on_domain a f == on_domain a g)
  = assert (on_domain a f == on_domain a g)
       by  (norm [delta_only [`%on_domain]];
            l_to_r (quote (quantifier_as_lemma sq_feq));
            t_trefl false)

let extensionality a b f g
  = let fwd a b (f g:arrow a b)
     : Lemma (requires feq #a #b f g)
             (ensures on_domain a f == on_domain a g)
             [SMTPat (feq #a #b f g)]
     = extensionality_1 a b f g ()
    in
    ()


(****** GTot version ******)

let on_domain_g (a:Type) (#b:a -> Type) (f:arrow_g a b)
  = fun (x:a) -> f x

let feq_on_domain_g (#a:Type) (#b:a -> Type) (f:arrow_g a b)
  = ()

let idempotence_on_domain_g #a #b f
  = assert_norm (on_domain_g a f == (on_domain_g a (on_domain_g a f)))

let extensionality_1_g (a:Type)
                       (b: a -> Type)
                       (f g: arrow_g a b)
                       (sq_feq : squash (feq_g f g))
  : Lemma (ensures on_domain_g a f == on_domain_g a g)
  = assert (on_domain_g a f == on_domain_g a g)
       by  (norm [delta_only [`%on_domain_g]];
            l_to_r (quote (quantifier_as_lemma sq_feq));
            t_trefl false)

let extensionality_g a b f g
  = let fwd a b (f g:arrow_g a b)
     : Lemma (requires feq_g #a #b f g)
             (ensures on_domain_g a f == on_domain_g a g)
             [SMTPat (feq_g #a #b f g)]
     = extensionality_1_g a b f g ()
    in
    ()
