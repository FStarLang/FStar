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

module FStar.Array

(**
F* standard library mutable arrays module.

@summary Mutable arrays
*)

open FStar.All
open FStar.Seq
open FStar.Ref

#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val array (a:Type0) : Type0

val as_ref (#a:Type0) (arr:array a) : GTot (ref (seq a))

let sel (#a:Type0) (h:heap) (s:array a) : GTot (seq a) = Heap.sel h (as_ref s)

let contains (#a:Type0) (h:heap) (s:array a) : Type0 = Heap.contains h (as_ref s)

let unused_in (#a:Type0) (arr:array a) (h:heap) : Type0 = Heap.unused_in (as_ref arr) h

let heap_upd (#a:Type0) (h:heap) (r:array a) (v:seq a) : GTot heap = Heap.upd h (as_ref r) v

let addr_of (#a:Type0) (arr:array a) : GTot nat = addr_of (as_ref arr)

let only (#a:Type0) (arr:array a) : GTot (Set.set nat) = Set.singleton (addr_of arr)

val op_At_Bar (#a:Type0) (s1:array a) (s2:array a)
  : ST (array a)
       (requires (fun h -> contains h s1 /\ contains h s2))
       (ensures  (fun h0 s h1 -> contains h0 s1 /\ contains h0 s2 /\ contains h1 s /\
                              sel h1 s == Seq.append (sel h0 s1) (sel h0 s2) /\
                              modifies Set.empty h0 h1))

unfold let create_post (#a:Type0) (s:seq a)
: heap -> array a -> heap -> Type0
= fun h0 x h1 ->
  x `unused_in` h0 /\
  contains h1 x /\
  modifies Set.empty h0 h1 /\
  sel h1 x== s
  
val of_seq (#a:Type0) (s:seq a)
: ST (array a)
  (requires fun _ -> True)
  (ensures create_post s)

val to_seq (#a:Type0) (s:array a)
  : ST (seq a)
       (requires (fun h -> contains h s))
       (ensures  (fun h0 x h1 -> (sel h0 s == x /\ h0 == h1)))

// Used by the compiler for array literals
val of_list (#a:Type0) (l:list a)
: ST (array a)
  (requires fun _ -> True)
  (ensures create_post (seq_of_list l))

val create (#a:Type0) (n:nat) (init:a)
  : ST (array a)
       (requires (fun h -> True))
       (ensures  (fun h0 x h1 -> x `unused_in` h0 /\
                              contains h1 x /\
                              modifies Set.empty h0 h1 /\
                              sel h1 x == Seq.create n init))

val index (#a:Type0) (x:array a) (n:nat)
  : ST a
       (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
       (ensures  (fun h0 v h1 -> n < Seq.length (sel h0 x) /\
                              h0 == h1 /\
                              v == Seq.index (sel h0 x) n))

val upd (#a:Type0) (x:array a) (n:nat) (v:a)
  :ST unit
      (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
      (ensures  (fun h0 u h1 -> n < Seq.length (sel h0 x) /\
                             contains h1 x /\
			     modifies (Set.singleton (addr_of x)) h0 h1 /\
			     sel h1 x == Seq.upd (sel h0 x) n v))

val length (#a:Type0) (x:array a)
  : ST nat
       (requires (fun h -> contains h x))
       (ensures  (fun h0 y h1 -> y = length (sel h0 x) /\ h0 == h1))

val op (#a:Type0) (f:seq a -> seq a) (x:array a)
  : ST unit
       (requires (fun h -> contains h x))
       (ensures  (fun h0 u h1 -> modifies (Set.singleton (addr_of x)) h0 h1 /\ sel h1 x == f (sel h0 x)))

val swap (#a:Type0) (x:array a) (i:nat) (j:nat{i <= j})
  : ST unit
       (requires (fun h -> contains h x /\ j < Seq.length (sel h x)))
       (ensures (fun h0 _u h1 -> j < Seq.length (sel h0 x) /\
                              contains h1 x /\
		              modifies (Set.singleton (addr_of x)) h0 h1 /\
		              sel h1 x == Seq.swap (sel h0 x) i j))

val copy (#a:Type0) (s:array a)
  : ST (array a)
       (requires (fun h -> contains h s /\ Seq.length (sel h s) > 0))
       (ensures (fun h0 r h1 -> modifies Set.empty h0 h1 /\
		             r `unused_in` h0 /\
                             contains h1 r /\
                             sel h1 r == sel h0 s))

val sub (#a:Type0) (s:array a) (idx:nat) (len:nat)
  : ST (array a)
       (requires (fun h -> contains h s /\
                         Seq.length (sel h s) > 0 /\
                         idx + len <= Seq.length (sel h s)))
    (ensures (fun h0 t h1 -> contains h1 t /\
                           t `unused_in` h0 /\
                           modifies Set.empty h0 h1 /\
                           Seq.slice (sel h0 s) idx (idx + len) == sel h1 t))
