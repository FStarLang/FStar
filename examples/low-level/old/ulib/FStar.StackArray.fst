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
module FStar.StackArray

//#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0" ... NEED TO MAKE THIS as_ref, as_ref, as_rref, ... a bit simpler

open FStar.Seq
open FStar.StackHeap2
open FStar.SST
open FStar.UInt32

module StackHeap = FStar.StackHeap2

let uint32 = UInt32.t

type bounded_seq (t:Type) = s:seq t{length s <= UInt.max_int n}
type array (t:Type) = ref (bounded_seq t)//NS: TODO if I change this to stacked, then I get unification failures elsewhere. seems like a bug

(* Commented for as long as not specified *)
// assume val op_At_Bar: #a:Type -> array a -> array a -> St (array a)

val of_seq: #a:Type -> s:bounded_seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun s0 x s1 -> (not(contains s0 x)
		             /\ frameOf x = top_frame_id s1
                             /\ contains s1 x
			     /\ frame_ids s1 = frame_ids s0
			     /\ modifies_one (top_frame_id s1) s0 s1
			     /\ modifies_ref (top_frame_id s1) !{as_ref x} s0 s1	                    
                             /\ sel s1 x =s)))
let of_seq #a s = salloc s

val to_seq: #a:Type -> s:array a -> ST (seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> sel h0 s=x /\ h0=h1))
let to_seq #a s = !s
  
val create : #a:Type -> n:uint32 -> init:a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> frame_ids h1 = frame_ids h0
		       /\ frameOf x = top_frame_id h1
		       /\ fresh_rref (as_rref x) h0 h1           //the rest of this is a bit more abstract than salloc; not sure if that's a good thing
		       /\ contains h1 x
		       /\ modifies_one (top_frame_id h1) h0 h1
		       /\ modifies_ref (top_frame_id h1) !{as_ref x} h0 h1	                    
		       /\ sel h1 x = Seq.create (v n) init
			     ))
let create #a n init = salloc (Seq.create (v n) init)

val index : #a:Type -> x:array a -> n:uint32 -> STL a
  (requires (fun h -> contains h x /\ v n < Seq.length (sel h x)))
  (ensures  (fun h0 res h1 -> v n < Seq.length (sel h0 x)
                       /\ h0=h1
                       /\ res=Seq.index (sel h0 x) (v n)))
let index #a x n = 
  let s = to_seq x in Seq.index s (v n) //TODO: Seem to need this eta nonsense ... if we get rid of the let binding, type inference fails

val upd : #a:Type -> x:array a -> n:uint32 -> z:a -> STL unit
  (requires (fun h -> contains h x /\ v n < Seq.length (sel h x)))
  (ensures  (fun h0 _ h1 -> (v n < Seq.length (sel h0 x)
                            /\ contains h1 x
			    /\ modifies (Set.singleton (frameOf x)) h0 h1
			    /\ modifies_ref (frameOf x) !{as_ref x} h0 h1
                            /\ h1==StackHeap.upd h0 x (Seq.upd (sel h0 x) (v n) z))))
let upd #a x n z = 
  let s = to_seq x in 
  let h0 = SST.get() in
  let s = Seq.upd s (v n) z in
  x := s;
  let h1 = SST.get() in
  cut (modifies_ref (frameOf x) !{as_ref x} h0 h1)

val length: #a:Type -> x:array a -> STL uint32
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> v y=length (sel h0 x) /\ h0==h1))
let length #a x = 
  let s = to_seq x in
  uint_to_t (Seq.length s)

let equal s1 s2 = 
  frame_ids s1 = frame_ids s2
  /\ Map.equal (heaps s1) (heaps s2)
  
val swap: #a:Type -> x:array a -> i:uint32 -> j:uint32{v i <= v j} -> STL unit 
  (requires (fun s -> contains s x /\ v j < Seq.length (sel s x)))
  (ensures (fun s0 _u s1 ->
    (v j < Seq.length (sel s0 x))
    /\ contains s1 x
    /\ modifies (Set.singleton (frameOf x)) s0 s1
    /\ modifies_ref (frameOf x) !{as_ref x} s0 s1
    /\ Seq.equal (StackHeap.sel s1 x) (Seq.swap (sel s0 x) (v i) (v j))))
let swap #a x i j =
  let h0 = get () in
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj
	 
let rec copy_aux: #a:Type -> s:array a -> cpy:array a -> ctr:uint32 -> ST unit
  (requires (fun h -> contains h s 
	       /\ contains h cpy 
	       /\ s <> cpy
	       /\ Seq.length (sel h cpy) = Seq.length (sel h s)
	       /\ v ctr <= Seq.length (sel h cpy)
	       /\ (forall (i:nat). i < v ctr ==> Seq.index (sel h s) i = Seq.index (sel h cpy) i)))
  (ensures (fun h0 u h1 -> contains h1 s 
		    /\ contains h1 cpy
		    /\ s <> cpy 
	            /\ modifies_one (frameOf cpy) h0 h1
		    /\ modifies_ref (frameOf cpy) !{as_ref cpy} h0 h1
		    /\ Seq.equal (sel h1 cpy) (sel h0 s)
		    /\ frame_ids h1 = frame_ids h0)) 
  = fun #a s cpy ctr -> 
    if (eq (length cpy) ctr) then ()
    else (upd cpy ctr (index s ctr);
	  copy_aux #a s cpy (ctr +^ (uint_to_t 1)))

val copy:
  #a:Type -> s:array a ->
  ST (array a) 
     (requires (fun h -> contains h s
			 /\ Seq.length (sel h s) > 0))
     (ensures (fun h0 r h1 -> modifies_one (top_frame_id h1) h0 h1
			    /\ modifies_ref (top_frame_id h1) !{as_ref s} h0 h1
	                    /\ frameOf r = top_frame_id h1
			    /\ not(contains h0 r)
			    /\ (contains h1 r)
			    /\ (Seq.equal (sel h1 r) (sel h0 s))))
let copy #a s =
  let cpy = create (length s) (index s (uint_to_t 0)) in
  copy_aux s cpy (uint_to_t 0);
  cpy

val blit_aux:
  #a:Type -> s:array a -> s_idx:uint32 -> t:array a -> t_idx:uint32 -> len:uint32 -> ctr:uint32 ->
  STL unit
     (requires (fun h ->
		(contains h s /\ contains h t /\ s <> t)
		/\ (Seq.length (sel h s) >= v s_idx + v len)
		/\ (Seq.length (sel h t) >= v t_idx + v len)
		/\ (v ctr <= v len)
		/\ (forall (i:nat).
		    i < v ctr ==> Seq.index (sel h s) (v s_idx+i) = Seq.index (sel h t) (v t_idx+i))))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ frame_ids h1 = frame_ids h0
               /\ modifies_one (frameOf t) h0 h1
	       /\ (modifies_ref (frameOf t) !{as_ref t} h0 h1)
	       /\ (Seq.length (sel h1 s) >= v s_idx + v len)
	       /\ (Seq.length (sel h1 t) >= v t_idx + v len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (forall (i:nat).
		   i < v len ==> Seq.index (sel h1 s) (v s_idx+i) = Seq.index (sel h1 t) (v t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < v t_idx \/ i >= v t_idx + v len)) ==>
		     Seq.index (sel h1 t) i = Seq.index (sel h0 t) i) ))

#reset-options "--z3timeout 20"

let rec blit_aux #a s s_idx t t_idx len ctr =
  let h0 = get() in
  if (len -^ ctr) =^ (uint_to_t 0) then ()
  else 
    begin 
      upd t (t_idx +^ ctr) (index s (s_idx +^ ctr));
      let h = SST.get() in
      cut (b2t(Heap.equal (heapOf t h) (Heap.upd (heapOf t h0) (as_ref t) (sel h t))));
      cut (Map.equal (heaps h) (heaps (StackHeap.upd h0 t (sel h t))));
      cut (sel h t = Seq.upd (sel h0 t) (v t_idx+v ctr) (Seq.index (sel h0 s) (v s_idx+v ctr)));
      cut (forall (i:nat). i < v ctr+1 ==> Seq.index (sel h0 s) (v s_idx+i) = Seq.index (sel h t) (v t_idx+i));
      assert(s <> t);
      blit_aux s s_idx t t_idx len (ctr+^(uint_to_t 1));
      let h'= get() in
      cut (modifies_ref (frameOf t) !{as_ref t} h h') (* JK: trigger *)
    end

#reset-options 
	 
val blit:
  #a:Type -> s:array a -> s_idx:uint32 -> t:array a -> t_idx:uint32 -> len:uint32 ->
  STL unit
     (requires (fun h ->
		(contains h s)
		/\ (contains h t)
		/\ (s <> t)
		/\ (Seq.length (sel h s) >= v s_idx + v len)
		/\ (Seq.length (sel h t) >= v t_idx + v len)))
     (ensures (fun h0 u h1 ->
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ frame_ids h1 = frame_ids h0
	       /\ (Seq.length (sel h1 s) >= v s_idx + v len)
	       /\ (Seq.length (sel h1 t) >= v t_idx + v len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (modifies_one (frameOf t) h0 h1)
	       /\ (modifies_ref (frameOf t) !{as_ref t} h0 h1)
	       /\ (forall (i:nat).
		   i < v len ==> Seq.index (sel h1 s) (v s_idx+i) = Seq.index (sel h1 t) (v t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < v t_idx \/ i >= v t_idx + v len)) ==>
		     (Seq.index (sel h1 t) i = Seq.index (sel h0 t) i)) ))
let rec blit #a s s_idx t t_idx len =
  blit_aux s s_idx t t_idx len (uint_to_t 0)

val sub :
  #a:Type -> s:array a -> idx:uint32 -> len:uint32 -> ST (array a)
    (requires (fun h -> contains h s
		      /\ Seq.length (sel h s) > 0
		      /\ v idx + v len <= Seq.length (sel h s) ))
    (ensures (fun h0 t h1 -> contains h1 t
			   /\ contains h0 s
			   /\ not(contains h0 t)
			   /\ modifies_one (top_frame_id h1) h0 h1
			   /\ modifies_ref (top_frame_id h1) !{as_ref t} h0 h1
			   /\ frameOf t = top_frame_id h1
			   /\ Seq.length (sel h0 s) > 0
			   /\ v idx + v len <= Seq.length (sel h0 s)
			   /\ Seq.equal (Seq.slice (sel h0 s) (v idx) (v idx+v len)) (sel h1 t) ))
let sub #a s idx len =
  let t = create len (index s (uint_to_t 0)) in
  blit s idx t (uint_to_t 0) len;
  t

(* JK: assuming the following because 'a <> a ==> seq a' <> seq a does cannot be proven
   by the solver *)
let lemma_array_ineq_1 (#a:Type) (#a':Type) (x:array a) (y:array a')
  : Lemma (requires (a <> a'))
	  (ensures (as_ref x =!= as_ref y))
	  [SMTPat (a <> a')]
  = admit() // TODO
