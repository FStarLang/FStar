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
module FStar.StackHeap2

open FStar.Map
open FStar.Heap

(* Region ids are just integers *)
abstract let rid = int
(* The root is 0, it is "reserved": 
   NS, BP: Do we really want to retain root? Not sure.
	   Stuff allocated there never goes away *)
abstract let root : rid = 0

//l0 `suffix_of` l1 is strict; i.e., l0 <> l1; RENAMED: used to be includes
//TODO: change this to be non-strict
val suffix_of: list rid -> list rid -> Tot bool
let rec suffix_of l0 l1 = 
  if List.Tot.length l0 >= List.Tot.length l1 then false
  else Cons.tl l1 = l0 || suffix_of l0 (Cons.tl l1) 

let is_valid_stack s = suffix_of [root] s

let t : Type0 = (frame_ids:list rid{is_valid_stack frame_ids} & //the stack will contain at least 1 element; used to be contains at least 2 elements; is that intentional?
	 m:Map.t rid heap{forall i. List.Tot.contains i frame_ids ==> Map.contains m i})

let mem : Type0 = t

(* Type of region references *)
(* Rewrote this a bit to avoid the assumes below *)
type stacked (a:Type) =
  | MkStacked : id:rid -> r:Heap.ref a -> stacked a

type rref (i:rid) (a:Type) = s:stacked a{s.id = i}

let frameOf #a (s:stacked a) = s.id

val as_rref : #a:Type -> s:stacked a -> Tot (rref s.id a)
let as_rref #a s = s

abstract val as_ref : #a:Type -> s:stacked a -> GTot (ref a)
let as_ref #a s = s.r

abstract val ref_as_rref : #a:Type -> i:rid -> r:ref a -> GTot (rref i a)
let ref_as_rref #a i r = MkStacked i r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj #a #i r = ()

(* Returns the stack of region ids *)
val frame_ids: t -> Tot (list rid)
let frame_ids s = dfst s

(* Returns the map of heaps corresponding to the region ids *)
val heaps: t -> Tot (Map.t rid heap)
let heaps s = dsnd s

(* s0 is a suffix of of s1, hence s0's references are readable and writable from s1 *)
abstract val is_parent: t -> t -> Tot bool
let is_parent s0 s1 = suffix_of (frame_ids s0) (frame_ids s1) 

(* Current frame id *)
val top_frame_id: s:t -> Tot rid
let top_frame_id s = Cons.hd (frame_ids s)

(* Current allocatable heap *)
val top_frame: s:t{frame_ids s <> []} -> Tot heap
let top_frame s = Map.sel (heaps s) (top_frame_id s)

(* Valid heap (the root frame is an ancestor *)
(* CHANGED THIS:
     Basically, it's poppable if it's valid after popping
*)     
//let valid (s:t) = includes [root] (frame_ids s) \/ frame_ids s = [root]
let poppable (s:t) = is_valid_stack (Cons.tl (dfst s))

(* Generates fresh region id *)
assume val fresh_rid: h:t -> Tot (r:rid{not(Map.contains (heaps h) r)})

let push_empty_frame (h:t) : Tot t =
  let id = fresh_rid h in
  (| id::frame_ids h,  Map.upd (heaps h) id Heap.emp |)
  
let pop_top_frame (h:t{poppable h}) : Tot t =
  (| Cons.tl (frame_ids h), heaps h |)

(* s1 has a new frame on top of s0. JK: Because of maps monotonicity I believe it 
   guaranties the unicity of the new frame id, needs to be checked *)
let fresh_frame (s0:t) (s1:t) = s1 = push_empty_frame s0
  (* Cons.tl (frame_ids s1) = frame_ids s0 /\      //the new stack extends the old one by just one frame *)
  (* not (Map.contains (heaps s0) (top_frame_id s1)) /\ //this new frame is not anywhere in the old stack *)
  (* (heaps s1 = Map.upd (heaps s0) (top_frame_id s1) emp) //and the new frame's heap is empty *)

(* Specifies untouched heaps *)
let modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict (Set.complement s) (heaps m0)))
  /\ Set.subset (Map.domain (heaps m0)) (Map.domain (heaps m1))

let modifies_top (m0:t) (m1:t) = frame_ids m0 = frame_ids m1 /\ modifies (Set.singleton (top_frame_id m1)) m0 m1

(* s01 is popped into s1 *)
let popped_stack (s0:t) (s1:t) = poppable s0 /\ s1 = pop_top_frame s0
  (* suffix_of [root] (frame_ids s0) /\  //again, seems vacuous *)
  (* Cons.tl (frame_ids s0) = frame_ids s1 /\  *)
  (* modifies Set.empty s1 s0 *)

let sel_rref (#a:Type) (#i:rid) (m:t) (r:rref i a) : a = Heap.sel (Map.sel (heaps m) i) (as_ref r)
let upd_rref (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) : t = 
  (|frame_ids m,  Map.upd (heaps m) i (Heap.upd (Map.sel (heaps m) i) (as_ref r) v)|)

let sel (#a:Type) (m:t) (r:stacked a) : a = sel_rref #a #r.id m r 
let upd (#a:Type) (m:t) (r:stacked a) (v:a) : t = upd_rref #a #r.id m r v

let modifies_one (r:rid) (m0:t) (m1:t) =
  Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict (Set.complement (Set.singleton r)) (heaps m0)))
  /\ Set.subset (Map.domain (heaps m0)) (Map.domain (heaps m1))

let equal_on (s:Set.set rid) (m0:t) (m1:t) =
 (forall (r:rid). {:pattern (Map.contains (heaps m0) r)} (Set.mem r s /\ Map.contains (heaps m0) r) ==> Map.contains (heaps m1) r)
 /\ Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict s (heaps m0)))

val lemma_modifies_trans: m1:t -> m2:t -> m3:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                                (ensures (modifies (Set.union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

let contains_rref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    List.Tot.contains i (frame_ids m) && Heap.contains (Map.sel (heaps m) i) (as_ref r)

let contains (#a:Type) (m:t) (r:stacked a) =
  contains_rref #a #r.id r m

let test (#a:Type) (s0:t) (r:stacked a{contains s0 r}) (v:a) =
  let s1 = upd s0 r v in assert(sel s1 r = v)

val upd_lemma: #a:Type -> s0:t -> s1:t -> x:stacked (FStar.Seq.seq a) -> j:nat -> tmpi:a ->
  Lemma (requires (j < Seq.length (sel s0 x) /\ s1==upd s0 x (Seq.upd (sel s0 x) j tmpi)))
	(ensures (j < Seq.length (sel s0 x) /\ sel s1 x = Seq.upd (sel s0 x) j tmpi))
let upd_lemma #a s0 s1 x j tmpi = ()	
  
let contains_frame (m:t) (id:rid) = List.Tot.contains id (frame_ids m)

let fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (contains_rref r m0) /\ contains_rref r m1

let fresh (#a:Type) (r:stacked a) (m0:t) (m1:t) = fresh_rref #a #r.id r m0 m1

let modifies_ref (r:rid) (s:Set.set aref) (s0:t) (s1:t) = 
  Heap.modifies s (Map.sel (heaps s0) r) (Map.sel (heaps s1) r)

val lemma_modifies_ref_1: #a:Type -> r:rid -> s:Set.set aref -> s0:t -> s1:t -> x:stacked a -> Lemma
  (requires (contains s0 x /\ modifies_ref r s s0 s1 /\ modifies_one r s0 s1 /\ 
		      (frameOf x <> r \/ (frameOf x = r /\ not(Set.mem (Ref (as_ref x)) s)))))
  (ensures (sel s1 x = sel s0 x))
  [SMTPat (modifies_ref r s s0 s1); SMTPat (~(Set.mem (Ref (as_ref x)) s))]
let lemma_modifies_ref_1 #a r s s0 s1 x = ()

val lemma_modifies_ref_2: #a:Type -> y:stacked a -> s0:t -> s1:t -> x:stacked a -> Lemma
  (requires (contains s0 x /\ modifies_ref (frameOf y) !{as_ref y} s0 s1 /\ modifies_one (frameOf y) s0 s1 /\ (frameOf x <> frameOf y \/ (frameOf x = frameOf y /\ y <> x))))
  (ensures (sel s1 x = sel s0 x))
  [SMTPat (modifies_ref (frameOf y) !{as_ref y} s0 s1); SMTPat (x <> y)]
let lemma_modifies_ref_2 #a y s0 s1 x = ()

open FStar.Set
let disjoint_regions (s1:set rid) (s2:set rid) = 
     forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> x <> y

val heapOf: #a:Type -> stacked a -> t -> Tot heap
let heapOf #a r s = Map.sel (heaps s) (frameOf r)

val asRef: #a:Type -> stacked a -> GTot (ref a)
let asRef #a r = as_ref r

let stacked_to_ref_lemma_1 (#a:Type) (x:stacked a) (y:stacked a)
  : Lemma (requires (x <> y /\ x.id=y.id))
	  (ensures (asRef x <> asRef y))
	  [SMTPat (x <> y)]
  = ()

let stacked_to_ref_lemma_2 (#a:Type) (x:stacked a) (y:stacked a)
  : Lemma (requires (x <> y /\ x.id=y.id))
	  (ensures (as_ref x <> as_ref y))
	  [SMTPat (x <> y)]
  = ()

let stack_to_ref_lemma_3 (#a:Type) (#a':Type) (x:stacked a) (y:stacked a')
  : Lemma (requires (a <> a'))
	  (ensures (as_ref x =!= as_ref y))
	  [SMTPat (a <> a')]
  = ()

(* Union of the domains of all the frames on the stack *)
let domain h : Tot (Set.set aref) =
  List.Tot.fold_left Set.union Set.empty (List.Tot.map (fun rid -> Heap.domain (Map.sel (heaps h) rid)) (frame_ids h))

let domain_equality (h:t) (h':t) : Type0 =
  frame_ids h = frame_ids h' /\ domain h = domain h'

assume val domain_equality_lemma_0: h0:t -> Lemma
  (requires (True))
  (ensures (domain_equality h0 (pop_top_frame (push_empty_frame h0))))
  [SMTPat (pop_top_frame (push_empty_frame h0))] 

val domain_equality_lemma_1: h0:t -> h1:t -> h2:t -> h3:t -> Lemma
  (requires (h1 = push_empty_frame h0 /\ frame_ids h2 = frame_ids h1
	     /\ domain_equality (pop_top_frame h1) (pop_top_frame h2)
	     /\ h3 = pop_top_frame h2))
  (ensures (domain_equality h0 h3))
  [SMTPat (h1 = push_empty_frame h0); SMTPat (frame_ids h2 = frame_ids h1);
   SMTPat (domain_equality (pop_top_frame h1) (pop_top_frame h2)); SMTPat (h3 = pop_top_frame h2)]
let domain_equality_lemma_1 h0 h1 h2 h3 = ()

assume val domain_equality_lemma_2: h0:t{poppable h0} -> h1:t{frame_ids h0 = frame_ids h1} -> Lemma
  (requires (modifies_one (top_frame_id h0) h0 h1))
  (ensures (domain_equality (pop_top_frame h0) (pop_top_frame h1)))
  [SMTPat (modifies_one (top_frame_id h0) h0 h1)]

assume val domain_equality_lemma_3: h0:t -> h1:t -> Lemma
  (requires (domain_equality h0 h1))
  (ensures (modifies_one (top_frame_id h0) h0 h1))
  [SMTPat (modifies_one (top_frame_id h0) h0 h1)]

assume val domain_equality_lemma_4: h:t -> h':t -> r:rid -> s:Set.set Heap.aref -> Lemma
  (requires (modifies (Set.singleton r) h h' /\ frame_ids h = frame_ids h' 
	    /\ modifies_ref r s h h' /\ modifies_ref r s h' h))
  (ensures (domain_equality h h'))
  [SMTPat (modifies_ref r s h h')]
