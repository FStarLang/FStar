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
module T = FStar.Tactics

let big_op_nil
      (#a:Type) (#b:Type) (#c:Type)
      (op:b -> c -> GTot c) (f:a -> GTot b) (z:c)
  : Lemma (map_op' op f [] z == z)
  = ()

let big_op_cons #a #b #c (op:b -> c -> GTot c) (f:a -> GTot b) (hd:a) (tl:list a) (z:c)
  : Lemma (map_op' op f (hd::tl) z == f hd `op` map_op' op f tl z)
  = ()

let big_and_nil (#a:Type) (f:a -> Type)
  : Lemma (big_and f [] == True)
  = ()

let big_and_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  : Lemma (big_and f (hd :: tl) == (f hd /\ big_and f tl))
  = ()

let big_or_nil (#a:Type) (f:a -> Type)
  : Lemma (big_or f [] == False)
  = ()

let big_or_cons (#a:Type) (f:a -> Type) (hd:a) (tl:list a)
  : Lemma (big_or f (hd :: tl) == (f hd \/ big_or f tl))
  = ()

let pairwise_and_nil (#a:Type) (f:a -> a -> Type0)
  : Lemma (pairwise_and f [] == True)
  = ()

let pairwise_and_cons (#a:Type) (f:a -> a -> Type0) (hd:a) (tl:list a)
  : Lemma (pairwise_and f (hd::tl) == (big_and (f hd) tl /\ pairwise_and f tl))
  = assert (pairwise_and f (hd::tl) == (big_and (f hd) tl /\ pairwise_and f tl) )
        by (T.trefl())

let pairwise_or_nil (#a:Type) (f:a -> a -> Type0)
  : Lemma (pairwise_or f [] == False)
  = ()

let pairwise_or_cons #a (f:a -> a -> Type0) (hd:a) (tl:list a)
  = assert (pairwise_or f (hd::tl) == (big_or (f hd) tl \/ pairwise_or f tl))
        by (T.trefl())

let rec big_and_forall (#a:Type) (f: a -> Type) (l:list a)
  : Lemma (big_and f l <==> (forall x. L.memP x l ==> f x))
  = match l with
    | [] -> ()
    | hd::tl ->
      big_and_cons f hd tl;
      big_and_forall f tl

let rec big_or_exists (#a:Type) (f: a -> Type) (l:list a)
  : Lemma (big_or f l <==> (exists x. L.memP x l /\ f x))
  = match l with
    | [] -> ()
    | hd::tl ->
      big_or_cons f hd tl;
      big_or_exists f tl
