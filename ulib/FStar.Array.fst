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

(**
F* standard library mutable arrays module.

@summary Mutable arrays
*)
module FStar.Array
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.All
open FStar.Seq
open FStar.Ref

abstract type array (t:Type) = ref (seq t)

abstract let as_ref (#a:Type) (arr:array a) : ref (seq a) = arr

let sel (#a:Type) (h:heap) (s:array a) = Heap.sel h (as_ref s)

let contains (#a:Type) (h:heap) (s:array a) : GTot bool =
  FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.contains h (as_ref s))

let unused_in (#a:Type) (arr:array a) (h:heap) : GTot bool
 = FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.unused_in (as_ref arr) h)

let heap_upd (#a:Type) (h:heap) (r:array a) (v:seq a) = Heap.upd h (as_ref r) v

let addr_of (#a:Type) (arr:array a) : GTot nat = addr_of (as_ref arr)

let only (#a:Type) (arr:array a) : GTot (Set.set nat) = Set.singleton (addr_of arr)

abstract val op_At_Bar: #a:Type -> s1:array a -> s2:array a -> ST (array a)
  (requires (fun h -> contains h s1 /\ contains h s2))
  (ensures  (fun h0 s h1 -> contains h0 s1 /\ contains h0 s2 /\ contains h1 s
    /\ sel h1 s == Seq.append (sel h0 s1) (sel h0 s2)
    /\ modifies Set.empty h0 h1))
let op_At_Bar #a s1 s2 =
  let s1' = !s1 in
  let s2' = !s2 in
  ST.alloc (Seq.append s1' s2')

abstract val of_seq: #a:Type -> s:seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (x `unused_in` h0
                             /\ contains h1 x
                             /\ modifies Set.empty h0 h1
                             /\ sel h1 x==s)))
let of_seq #a s =
  ST.alloc s

abstract val to_seq: #a:Type -> s:array a -> ST (seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> (sel h0 s==x /\ h0==h1)))
let to_seq #a s =
  !s

abstract val create : #a:Type -> n:nat -> init:a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (x `unused_in` h0
                             /\ contains h1 x
                             /\ modifies Set.empty h0 h1
                             /\ sel h1 x==Seq.create n init)))
  (* (ensures  (fun h0 x h1 -> (~ (contains h0 x) *)
  (*                            /\ contains h1 x *)
  (*                            /\ modifies Set.empty h0 h1 *)
  (*                            /\ sel h1 x==Seq.create n init))) *)
let create #a n init =
  ST.alloc (Seq.create n init)

abstract val index : #a:Type -> x:array a -> n:nat -> ST a
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 v h1 -> (n < Seq.length (sel h0 x)
                             /\ h0==h1
                             /\ v==Seq.index (sel h0 x) n)))
let index #a x n =
  let s = to_seq x in
  Seq.index s n

abstract val upd : #a:Type -> x:array a -> n:nat -> v:a -> ST unit
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 u h1 -> (n < Seq.length (sel h0 x)
                            /\ contains h1 x
			    /\ modifies (Set.singleton (addr_of x)) h0 h1
			    /\ sel h1 x == Seq.upd (sel h0 x) n v)))
let upd #a x n v =
  let s = !x in
  let s' = Seq.upd s n v in
  x:= s'

abstract val length: #a:Type -> x:array a -> ST nat
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> y=length (sel h0 x) /\ h0==h1))
let length #a x =
  let s = !x in Seq.length s

abstract val op: #a:Type -> f:(seq a -> Tot (seq a)) -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures  (fun h0 u h1 -> modifies (Set.singleton (addr_of x)) h0 h1 /\ sel h1 x==f (sel h0 x)))
let op #a f x =
  let s = !x in
  let s' = f s in
  x := s'

val swap: #a:Type -> x:array a -> i:nat -> j:nat{i <= j}
                 -> ST unit (requires (fun h -> contains h x /\ j < Seq.length (sel h x)))
                            (ensures (fun h0 _u h1 ->
                                      (j < Seq.length (sel h0 x))
                                      /\ contains h1 x
				      /\ modifies (Set.singleton (addr_of x)) h0 h1
				      /\ sel h1 x == Seq.swap (sel h0 x) i j))
let swap #a x i j =
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj

(* Helper functions for stateful array manipulation *)
val copy_aux:
  #a:Type -> s:array a -> cpy:array a -> ctr:nat ->
     ST unit
	(requires (fun h -> (contains h s /\ contains h cpy /\ addr_of s <> addr_of cpy)
			    /\ (Seq.length (sel h cpy) = Seq.length (sel h s))
			    /\ (ctr <= Seq.length (sel h cpy))
			    /\ (forall (i:nat). i < ctr ==> Seq.index (sel h s) i == Seq.index (sel h cpy) i)))
	(ensures (fun h0 u h1 -> (contains h1 s /\ contains h1 cpy /\ addr_of s <> addr_of cpy )
			      /\ (modifies (only cpy) h0 h1)
			      /\ (Seq.equal (sel h1 cpy) (sel h1 s))))
let rec copy_aux #a s cpy ctr =
  match length cpy - ctr with
  | 0 -> ()
  | _ -> upd cpy ctr (index s ctr);
	 copy_aux s cpy (ctr+1)

val copy:
  #a:Type -> s:array a ->
  ST (array a)
     (requires (fun h -> contains h s
			 /\ Seq.length (sel h s) > 0))
     (ensures (fun h0 r h1 -> (modifies Set.empty h0 h1)
				     /\ r `unused_in` h0
				     /\ (contains h1 r)
				     /\ (Seq.equal (sel h1 r) (sel h0 s))))
let copy #a s =
  let cpy = create (length s) (index s 0) in
  copy_aux s cpy 0;
  cpy

val blit_aux:
  #a:Type -> s:array a -> s_idx:nat -> t:array a -> t_idx:nat -> len:nat -> ctr:nat ->
  ST unit
     (requires (fun h ->
		(contains h s /\ contains h t /\ addr_of s <> addr_of t)
		/\ (Seq.length (sel h s) >= s_idx + len)
		/\ (Seq.length (sel h t) >= t_idx + len)
		/\ (ctr <= len)
		/\ (forall (i:nat).
		    i < ctr ==> Seq.index (sel h s) (s_idx+i) == Seq.index (sel h t) (t_idx+i))))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ addr_of s <> addr_of t)
	       /\ (modifies (only t) h0 h1)
	       /\ (Seq.length (sel h1 s) >= s_idx + len)
	       /\ (Seq.length (sel h1 t) >= t_idx + len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (forall (i:nat).
		   i < len ==> Seq.index (sel h1 s) (s_idx+i) == Seq.index (sel h1 t) (t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < t_idx \/ i >= t_idx + len)) ==>
		     Seq.index (sel h1 t) i == Seq.index (sel h0 t) i) ))

#set-options "--z3rlimit 60"
let rec blit_aux #a s s_idx t t_idx len ctr =
  match len - ctr with
  | 0 -> ()
  | _ -> upd t (t_idx + ctr) (index s (s_idx + ctr));
         blit_aux s s_idx t t_idx len (ctr+1)
#set-options "--z3rlimit 5"

private val blit:
  #a:Type -> s:array a -> s_idx:nat -> t:array a -> t_idx:nat -> len:nat ->
  ST unit
     (requires (fun h ->
		(contains h s)
		/\ (contains h t)
		/\ (addr_of s <> addr_of t)
		/\ (Seq.length (sel h s) >= s_idx + len)
		/\ (Seq.length (sel h t) >= t_idx + len)))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ addr_of s <> addr_of t)
	       /\ (Seq.length (sel h1 s) >= s_idx + len)
	       /\ (Seq.length (sel h1 t) >= t_idx + len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (modifies (only t) h0 h1)
	       /\ (forall (i:nat).
		   i < len ==> Seq.index (sel h1 s) (s_idx+i) == Seq.index (sel h1 t) (t_idx+i))
	       /\ (forall (i:nat).{:pattern (Seq.index (sel h1 t) i)}
		   (i < Seq.length (sel h1 t) /\ (i < t_idx \/ i >= t_idx + len)) ==>
		     (Seq.index (sel h1 t) i == Seq.index (sel h0 t) i)) ))
let rec blit #a s s_idx t t_idx len =
  blit_aux s s_idx t t_idx len 0

val sub :
  #a:Type -> s:array a -> idx:nat -> len:nat ->
  ST (array a)
    (requires (fun h ->
      (contains h s)
      /\ (Seq.length (sel h s) > 0)
      /\ (idx + len <= Seq.length (sel h s))))
    (ensures (fun h0 t h1 ->
      (contains h1 t)
      /\ (contains h0 s)
      /\ t `unused_in` h0
      /\ (modifies Set.empty h0 h1)
      /\ (Seq.length (sel h0 s) > 0)
      /\ (idx + len <= Seq.length (sel h0 s))
      /\ (Seq.equal (Seq.slice (sel h0 s) idx (idx+len)) (sel h1 t))))

#set-options "--z3rlimit 120"
let sub #a s idx len =
  let t = create len (index s 0) in
  blit s idx t 0 len;
  t
