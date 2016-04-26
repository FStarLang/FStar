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
module FStar.MachineArray
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

open FStar.Seq
open FStar.Heap
open FStar.UInt.UInt32

type bounded_seq (t:Type) = s:seq t{length s <= UInt.max_int n} 
type array (t:Type) = ref (bounded_seq t)

type uint32 = uint32

val of_seq: #a:Type -> s:bounded_seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x)
                             /\ contains h1 x
                             /\ modifies !{} h0 h1
                             /\ sel h1 x=s)))
let of_seq #a s = alloc s

val to_seq: #a:Type -> s:array a -> ST (bounded_seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> (sel h0 s=x /\ h0==h1)))
let to_seq #a s = !s

val create : #a:Type -> n:uint32 -> init:a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x)
                             /\ contains h1 x
                             /\ modifies !{} h0 h1
                             /\ sel h1 x=Seq.create (v n) init)))
let create #a n init =
  let s = Seq.create (v n) init in of_seq s

val index : #a:Type -> x:array a -> n:uint32 -> ST a
  (requires (fun h -> contains h x /\ v n < Seq.length (sel h x)))
  (ensures  (fun h0 z h1 -> (v n < Seq.length (sel h0 x)
                             /\ h0==h1
                             /\ z=Seq.index (sel h0 x) (v n))))
let index #a x n = 
  let s = to_seq x in
  Seq.index s (v n)

val upd : #a:Type -> x:array a -> n:uint32 -> z:a -> ST unit
  (requires (fun h -> contains h x /\ v n < Seq.length (sel h x)))
  (ensures  (fun h0 u h1 -> (v n < Seq.length (sel h0 x)
                            /\ contains h1 x
                            /\ h1==upd h0 x (Seq.upd (sel h0 x) (v n) z))))
let upd #a x n z =
  let s = to_seq x in
  let s' = Seq.upd s (v n) z in
  x := s'

val length: #a:Type -> x:array a -> ST uint32
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> v y=length (sel h0 x) /\ h0==h1))
let length #a x = let s = to_seq x in int_to_uint32 (Seq.length s)

val op: #a:Type -> f:(bounded_seq a -> Tot (bounded_seq a)) -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures  (fun h0 u h1 -> modifies !{x} h0 h1 /\ sel h1 x=f (sel h0 x)))
let op #a f x = 
  let s = to_seq x in
  let s' = f s in
  x := s'

val swap: #a:Type -> x:array a -> i:uint32 -> j:uint32{v i <= v j}
                 -> ST unit (requires (fun h -> contains h x /\ v j < Seq.length (sel h x)))
                            (ensures (fun h0 _u h1 ->
                                      (v j < Seq.length (sel h0 x))
                                      /\ contains h1 x
                                      /\ (h1==Heap.upd h0 x (SeqProperties.swap (sel h0 x) (v i) (v j)))))
let swap #a x i j =
  let h0 = get () in
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj;
  let h1 = get () in
  let s1 = sel h1 x in
  cut (b2t(equal h1 (Heap.upd h0 x s1)))

(* Helper functions for stateful array manipulation *)
val copy_aux:
  #a:Type -> s:array a -> cpy:array a -> ctr:uint32 ->
     ST unit
	(requires (fun h -> (contains h s /\ contains h cpy /\ s <> cpy)
			    /\ (Seq.length (sel h cpy) = Seq.length (sel h s))
			    /\ (v ctr <= Seq.length (sel h cpy))
			    /\ (forall (i:nat). i < v ctr ==> Seq.index (sel h s) i = Seq.index (sel h cpy) i)))
	(ensures (fun h0 u h1 -> (contains h1 s /\ contains h1 cpy /\ s <> cpy )
			      /\ (modifies !{cpy} h0 h1)
			      /\ (Seq.equal (sel h1 cpy) (sel h1 s))))
let rec copy_aux #a s cpy ctr =
  if (eq (length cpy) ctr) then ()
  else (upd cpy ctr (index s ctr);
       copy_aux s cpy (ctr ^+ one))

val copy:
  #a:Type -> s:array a ->
  ST (array a)
     (requires (fun h -> contains h s
			 /\ Seq.length (sel h s) > 0))
     (ensures (fun h0 r h1 -> (modifies !{} h0 h1)
				     /\ not(contains h0 r)
				     /\ (contains h1 r)
				     /\ (Seq.equal (sel h1 r) (sel h0 s))))
let copy #a s =
  let cpy = create (length s) (index s zero) in
  copy_aux s cpy zero;
  cpy

val blit_aux:
  #a:Type -> s:array a -> s_idx:uint32 -> t:array a -> t_idx:uint32 -> len:uint32 -> ctr:uint32 ->
  ST unit
     (requires (fun h ->
		(contains h s /\ contains h t /\ s <> t)
		/\ (Seq.length (sel h s) >= v s_idx + v len)
		/\ (Seq.length (sel h t) >= v t_idx + v len)
		/\ (v ctr <= v len)
		/\ (forall (i:nat).
		    i < v ctr ==> Seq.index (sel h s) (v s_idx+i) = Seq.index (sel h t) (v t_idx+i))))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ (modifies !{t} h0 h1)
	       /\ (Seq.length (sel h1 s) >= v s_idx + v len)
	       /\ (Seq.length (sel h1 t) >= v t_idx + v len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (forall (i:nat).
		   i < v len ==> Seq.index (sel h1 s) (v s_idx+i) = Seq.index (sel h1 t) (v t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < v t_idx \/ i >= v t_idx + v len)) ==>
		     Seq.index (sel h1 t) i = Seq.index (sel h0 t) i) ))
let rec blit_aux #a s s_idx t t_idx len ctr =
  if (len ^- ctr) ^= zero then ()
  else 
    begin 
      let h = ST.get() in
      upd t (t_idx ^+ ctr) (index s (s_idx ^+ ctr));
      blit_aux s s_idx t t_idx len (ctr^+one)
    end

val blit:
  #a:Type -> s:array a -> s_idx:uint32 -> t:array a -> t_idx:uint32 -> len:uint32 ->
  ST unit
     (requires (fun h ->
		(contains h s)
		/\ (contains h t)
		/\ (s <> t)
		/\ (Seq.length (sel h s) >= v s_idx + v len)
		/\ (Seq.length (sel h t) >= v t_idx + v len)))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ (Seq.length (sel h1 s) >= v s_idx + v len)
	       /\ (Seq.length (sel h1 t) >= v t_idx + v len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (modifies !{t} h0 h1)
	       /\ (forall (i:nat).
		   i < v len ==> Seq.index (sel h1 s) (v s_idx+i) = Seq.index (sel h1 t) (v t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < v t_idx \/ i >= v t_idx + v len)) ==>
		     (Seq.index (sel h1 t) i = Seq.index (sel h0 t) i)) ))
let rec blit #a s s_idx t t_idx len =
  blit_aux s s_idx t t_idx len zero

val sub :
  #a:Type -> s:array a -> idx:uint32 -> len:uint32 ->
  ST (array a)
    (requires (fun h ->
      (contains h s)
      /\ (Seq.length (sel h s) > 0)
      /\ (v idx + v len <= Seq.length (sel h s))))
    (ensures (fun h0 t h1 ->
      (contains h1 t)
      /\ (contains h0 s)
      /\ not(contains h0 t)
      /\ (modifies !{} h0 h1)
      /\ (Seq.length (sel h0 s) > 0)
      /\ (v idx + v len <= Seq.length (sel h0 s))
      /\ (Seq.equal (Seq.slice (sel h0 s) (v idx) (v idx + v len)) (sel h1 t))))
let sub #a s idx len =
  let t = create len (index s zero) in
  blit s idx t zero len;
  t
