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
module FStar.MRef
open FStar.Heap
open FStar.ST

open FStar.Preorder

let stable = FStar.Preorder.stable

val token (#a:Type) (#b:preorder a) (r:mref a b) (p:(a -> Type){stable p b}) : Type0

val witness_token: #a:Type -> #b:preorder a -> m:mref a b -> p:(a -> Type){stable p b}
  -> ST unit (requires (fun h0 -> p (sel h0 m)))
            (ensures (fun h0 _ h1 -> h0==h1 /\ token m p))

val recall_token: #a:Type -> #b:preorder a -> m:mref a b -> p:(a -> Type){stable p b}
  -> ST unit (requires (fun _ ->  token m p))
            (ensures (fun h0 _ h1 -> h0==h1 /\ p (sel h1 m)))

let spred (#a:Type) (rel:preorder a) = p:(a -> Type){Preorder.stable p rel}

val lemma_functoriality (#a:Type) (#rel:preorder a) (r:mref a rel) (p q:spred rel)
  : Lemma (requires (token r p /\ (forall x. p x ==> q x)))
    (ensures (token r q))

(* KM : These don't have much to do here... *)

val recall: p:(heap -> Type){ST.stable p} ->
  ST unit
    (requires (fun _ ->  witnessed p))
    (ensures (fun h0 _ h1 -> h0 == h1 /\ p h1))

val witness: p:(heap -> Type){ST.stable p} ->
  ST unit
    (requires (fun h0 -> p h0))
    (ensures (fun h0 _ h1 -> h0==h1 /\ witnessed p))
