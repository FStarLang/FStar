(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(* Mutable arrays *)
module Array
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open Seq
open ST
open Heap
(* private *) type array (t:Type) = ref (seq t)

assume val op_At_Bar: a:Type -> array a -> array a -> Prims.St (array a)

assume val of_seq: a:Type -> s:seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x)
                             /\ contains h1 x
                             /\ sel h1 x=s)))
  (modifies no_refs)

assume val to_seq: a:Type -> s:array a -> St (seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> (sel h0 s=x /\ h0==h1)))

assume val create : a:Type -> n:nat -> init:a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x)
                             /\ contains h1 x
                             /\ sel h1 x=Seq.create n init)))
  (modifies no_refs)

assume val index : a:Type -> x:array a -> n:nat -> St a
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 v h1 -> (n < Seq.length (sel h0 x)
                             /\ h0==h1
                             /\ v=Seq.index (sel h0 x) n)))


assume val upd : a:Type -> x:array a -> n:nat -> v:a -> ST unit
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 u h1 -> (n < Seq.length (sel h0 x)
                            /\ contains h1 x
                            /\ h1==upd h0 x (Seq.upd (sel h0 x) n v))))
  (modifies (a_ref x))

assume val length: a:Type -> x:array a -> St nat
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> y=length (sel h0 x) /\ h0==h1))

assume val op: a:Type -> f:(seq a -> Tot (seq a)) -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures  (fun h0 u h1 -> sel h1 x=f (sel h0 x)))
  (modifies (a_ref x))


val swap: a:Type -> x:array a -> i:nat -> j:nat{i <= j}
                 -> St unit (requires (fun h -> contains h x /\ j < Seq.length (sel h x)))
                            (ensures (fun h0 _u h1 ->
                                      (j < Seq.length (sel h0 x))
                                      /\ contains h1 x
                                      /\ (h1==Heap.upd h0 x (SeqProperties.swap (sel h0 x) i j))))
let swap x i j =
  let h0 = get () in
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj;
  let h1 = get () in
  let s1 = sel h1 x in
  cut (b2t(equal h1 (Heap.upd h0 x s1)))
