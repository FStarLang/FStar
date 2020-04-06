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
module Bug463a

open FStar.List.Tot

val list_subterm_ordering_coercion:
  l:list 'a
  -> bound:'b{l << bound}
  -> Tot (m:list 'a{l==m /\ (forall (x:'a). mem x m ==> x << bound)})

let rec list_subterm_ordering_coercion l bound = match l with
  | [] -> []
  | hd::tl ->
    hd::list_subterm_ordering_coercion tl bound

(* WARNING: pattern does not contain all quantified variables. *)
val list_subterm_ordering_lemma:
  l:list 'a
  -> bound:'b
  -> x:'a
  -> Lemma (requires (l << bound))
          (ensures (mem x l ==> x << bound))
          [SMTPat (mem x l); SMTPat (x << bound)]

let rec list_subterm_ordering_lemma l bound x = match l with
  | [] -> ()
  | hd::tl -> list_subterm_ordering_lemma tl bound x

val move_refinement:
  #a:Type
  -> #p:(a -> Type)
  -> l:list a{forall z. mem z l ==> p z}
  -> Tot (list (x:a{p x}))

let rec move_refinement (#a:Type) (#p:(a -> Type)) l = match l with
  | [] -> []
  | hd::tl -> hd::move_refinement #a #p tl

val lemma_move_refinement_length:
  #a:Type
  -> #p:(a -> Type)
  -> l:list a{forall z. mem z l ==> p z}
  -> Lemma (requires (True))
          (ensures ((length l) = (length (move_refinement #a #p l))))
          [SMTPat (move_refinement #a #p l)]

let rec lemma_move_refinement_length (#a:Type) (#p:(a -> Type)) l =
  match l with
  | [] -> ()
  | hd::tl -> lemma_move_refinement_length #a #p tl
