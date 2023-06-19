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
module FStar.BigOps
module T = FStar.Tactics.V2

let normal_eq (#a:Type) (f:a)
  = ()

////////////////////////////////////////////////////////////////////////////////
let map_op'_nil
      (#a:Type) (#b:Type) (#c:Type)
      (op:b -> c -> GTot c) (f:a -> GTot b) (z:c)
  : Lemma (map_op' op f [] z == z)
  = ()

let map_op'_cons #a #b #c (op:b -> c -> GTot c) (f:a -> GTot b) (hd:a) (tl:list a) (z:c)
  : Lemma (map_op' op f (hd::tl) z == f hd `op` map_op' op f tl z)
  = ()

////////////////////////////////////////////////////////////////////////////////
let big_and'_nil (#a:Type) (f:a -> Type)
  = assert (big_and' f [] == True) by (T.compute())

let big_and'_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  = assert (big_and' f (hd :: tl) == (f hd /\ big_and' f tl)) by (T.compute())

let big_and'_prop (#a:Type) (f:a -> Type) (l:list a)
  = match l with
    | [] -> big_and'_nil f
    | hd::tl -> big_and'_cons f hd tl

let rec big_and'_forall (#a:Type) (f:a -> Type) (l:list a)
  = match l with
    | [] -> big_and'_nil f; ()
    | hd::tl -> big_and'_cons f hd tl; big_and'_forall f tl

////////////////////////////////////////////////////////////////////////////////
let big_or'_nil (#a:Type) (f:a -> Type)
  = assert (big_or' f [] == False) by (T.compute())

let big_or'_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  = assert (big_or' f (hd :: tl) == (f hd \/ big_or' f tl)) by (T.compute())

let big_or'_prop (#a:Type) (f:a -> Type) (l:list a)
  = match l with
    | [] -> big_or'_nil f
    | hd::tl -> big_or'_cons f hd tl

let rec big_or'_exists (#a:Type) (f:a -> Type) (l:list a)
  = match l with
    | [] -> big_or'_nil f; ()
    | hd::tl -> big_or'_cons f hd tl; big_or'_exists f tl

////////////////////////////////////////////////////////////////////////////////
let pairwise_and'_nil (#a:Type) (f:a -> a -> Type0)
  = assert (pairwise_and' f [] == True) by (T.compute())

let pairwise_and'_cons (#a:Type) (f:a -> a -> Type) (hd:a) (tl:list a)
  = assert (pairwise_and' f (hd::tl) == (big_and' (f hd) tl /\ pairwise_and' f tl))
        by (T.trefl())

let pairwise_and'_prop (#a:Type) (f:a -> a -> Type) (l:list a)
  = match l with
    | [] -> pairwise_and'_nil f
    | hd::tl -> pairwise_and'_cons f hd tl

(* Note, this is good example of where the difference between
   the implicitly and explicitly reducing variants of the definitions
   makes a difference.

   Proving this lemma directly on the `pairwise_and` is much harder
   since one has to reason about many partially reduced forms.

   Instead, we first prove the lemma on the non-reducing primed
   version of the definition, and then obtain the lemma we want
   at the end using `normal_eq` *)
let rec pairwise_and'_forall (#a:Type) (f: a -> a -> Type) (l:list a)
  = match l with
    | [] -> pairwise_and'_nil f
    | hd::tl ->
      pairwise_and'_cons f hd tl;
      pairwise_and'_forall f tl;
      big_and'_forall (f hd) tl

let rec pairwise_and'_forall_no_repeats (#a:Type) (f: a -> a -> Type) (l:list a)
  = match l with
    | [] -> pairwise_and'_nil f
    | hd::tl ->
      pairwise_and'_cons f hd tl;
      pairwise_and'_forall_no_repeats f tl;
      big_and'_forall (f hd) tl
////////////////////////////////////////////////////////////////////////////////

let pairwise_or'_nil (#a:Type) (f:a -> a -> Type0)
  = assert (pairwise_or' f [] == False) by (T.compute())

let pairwise_or'_cons (#a:Type) (f:a -> a -> Type) (hd:a) (tl:list a)
  = assert (pairwise_or' f (hd::tl) == (big_or' (f hd) tl \/ pairwise_or' f tl))

let pairwise_or'_prop (#a:Type) (f:a -> a -> Type) (l:list a)
  = match l with
    | [] -> pairwise_or'_nil f
    | hd::tl -> pairwise_or'_cons f hd tl

let rec pairwise_or'_exists (#a:Type) (f: a -> a -> Type) (l:list a)
  = match l with
    | [] -> pairwise_or'_nil f
    | hd::tl ->
      pairwise_or'_cons f hd tl;
      pairwise_or'_exists f tl;
      big_or'_exists (f hd) tl

let rec pairwise_or'_exists_no_repeats (#a:Type) (f: a -> a -> Type) (l:list a)
  = match l with
    | [] -> pairwise_or'_nil f
    | hd::tl ->
      pairwise_or'_cons f hd tl;
      pairwise_or'_exists_no_repeats f tl;
      big_or'_exists (f hd) tl
