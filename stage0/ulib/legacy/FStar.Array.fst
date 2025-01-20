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

let array a = ref (seq a)

let as_ref #_ arr = arr

let op_At_Bar #a s1 s2 =
  let s1' = !s1 in
  let s2' = !s2 in
  ST.alloc (Seq.append s1' s2')

let of_seq #a s = ST.alloc s

let to_seq #a s = !s

let of_list #a l = of_seq (Seq.seq_of_list l)

let create #a n init = ST.alloc (Seq.create n init)

let index #a x n =
  let s = to_seq x in
  Seq.index s n

let upd #a x n v =
  let s = !x in
  let s' = Seq.upd s n v in
  x:= s'

let length #a x = let s = !x in Seq.length s

let op #a f x =
  let s = !x in
  let s' = f s in
  x := s'

let swap #a x i j =
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj

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

let copy #a s =
  let cpy = create (length s) (index s 0) in
  copy_aux s cpy 0;
  cpy

private val blit_aux:
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
let blit #a s s_idx t t_idx len =
  blit_aux s s_idx t t_idx len 0

#set-options "--z3rlimit 120"
let sub #a s idx len =
  let h0 = ST.get () in
  let t = create len (index s 0) in
  blit s idx t 0 len;
  let h1 = ST.get () in
  assert (Seq.equal (Seq.slice (sel h0 s) idx (idx + len)) (sel h1 t));
  t
