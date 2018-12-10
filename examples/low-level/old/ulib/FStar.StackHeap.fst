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
module FStar.StackHeap

open FStar.Map
open FStar.Heap

(* Region ids are just integers *)
abstract let rid = int
(* The root is 0, it is "reserved" *)
abstract let root : rid = 0

val includes: list rid -> list rid -> Tot bool
let rec includes l0 l1 = 
  if List.Tot.length l0 >= List.Tot.length l1 then false
  else Cons.tl l1 = l0 || includes l0 (Cons.tl l1)

let t = (id:list rid{includes [root] id} & m:Map.t rid heap{forall i. List.Tot.contains i id ==> Map.contains m i})

let mem = t

(* Type of region references *)
abstract let rref (id:rid) (a:Type) = Heap.ref a

(* Abstract uniform reprensetation of the values allocated on the stack *)
assume new type stacked : Type -> Type
assume val frameOf: #a:Type -> stacked a -> Tot rid
assume val refOf: #a:Type -> s:stacked a -> Tot (rref (frameOf s) a)

abstract val as_ref : #a:Type -> #id:rid -> r:rref id a -> Tot (ref a)
let as_ref #a #id r = r

abstract val ref_as_rref : i:rid -> r:ref 'a -> GTot (rref i 'a)
let ref_as_rref i r = r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj #a #i r = ()

(* Returns the stack of region ids *)
val stack: t -> Tot (list rid)
let stack s = dfst s

(* Returns the map of heaps corresponding to the region ids *)
val heaps: t -> Tot (Map.t rid heap)
let heaps s = dsnd s

(* s0 is a prefix of s1, hence s0's references are readable and writable from s1 *)
abstract val is_parent: t -> t -> Tot bool
let is_parent s0 s1 = includes (stack s0) (stack s1)

(* Current frame id *)
val top_frame_id: s:t -> Tot rid
let top_frame_id s = Cons.hd (stack s)

(* Current allocatable heap *)
val top_frame: s:t{stack s <> []} -> Tot heap
let top_frame s = Map.sel (heaps s) (top_frame_id s)

(* Valid heap (the root frame is an ancestor *)
//let valid (s:t) = includes [root] (stack s) \/ stack s = [root]
let poppable (s:t) = includes [root] (stack s)

(* s1 has a new frame on top of s0. JK: Because of maps monotonicity I believe it 
   guaranties the unicity of the new frame id, needs to be checked *)
let fresh_frame (s0:t) (s1:t) = 
  includes [root] (stack s1) /\ Cons.tl (stack s1) = stack s0
  /\ not (Map.contains (heaps s0) (top_frame_id s1))
  /\ (heaps s1 = Map.upd (heaps s0) (top_frame_id s1) emp)

(* Specifies untouched heaps *)
let modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict (Set.complement s) (heaps m0)))

let modifies_top (m0:t) (m1:t) = stack m0 = stack m1 /\ modifies (Set.singleton (top_frame_id m1)) m0 m1

(* s0 is popped into s1 *)
let popped_stack (s0:t) (s1:t) =
  includes [root] (stack s0) /\ Cons.tl (stack s0) = stack s1
  /\ modifies Set.empty s1 s0

let sel_rref (#a:Type) (#i:rid) (m:t) (r:rref i a) : a = Heap.sel (Map.sel (heaps m) i) (as_ref r)
let upd_rref (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) : t = 
  (|stack m,  Map.upd (heaps m) i (Heap.upd (Map.sel (heaps m) i) (as_ref r) v)|)

let sel (#a:Type) (m:t) (r:stacked a) : a = sel_rref m (refOf r)
let upd (#a:Type) (m:t) (r:stacked a) (v:a) : t = upd_rref m (refOf r) v

let modifies_one (r:rid) (m0:t) (m1:t) =
  Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict (Set.complement (Set.singleton r)) (heaps m0)))

let equal_on (s:Set.set rid) (m0:t) (m1:t) =
 (forall (r:rid). {:pattern (Map.contains (heaps m0) r)} (Set.mem r s /\ Map.contains (heaps m0) r) ==> Map.contains (heaps m1) r)
 /\ Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict s (heaps m0)))

val lemma_modifies_trans: m1:t -> m2:t -> m3:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                                (ensures (modifies (Set.union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

let contains_rref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    List.Tot.contains i (stack m) && Heap.contains (Map.sel (heaps m) i) (as_ref r)

let contains (#a:Type) (m:t) (r:stacked a) =
  contains_rref (refOf r) m

let test (#a:Type) (s0:t) (r:stacked a{contains s0 r}) (v:a) =
  let s1 = upd s0 r v in assert(sel s1 r = v)

val upd_lemma: #a:Type -> s0:t -> s1:t -> x:stacked (FStar.Seq.seq a) -> j:nat -> tmpi:a ->
  Lemma (requires (j < Seq.length (sel s0 x) /\ s1==upd s0 x (Seq.upd (sel s0 x) j tmpi)))
	(ensures (j < Seq.length (sel s0 x) /\ sel s1 x = Seq.upd (sel s0 x) j tmpi))
let upd_lemma #a s0 s1 x j tmpi = ()	
  
let contains_frame (m:t) (id:rid) = List.Tot.contains id (stack m)

let fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (contains_rref r m0) /\ contains_rref r m1

let fresh (#a:Type) (r:stacked a) (m0:t) (m1:t) = fresh_rref (refOf r) m0 m1

let modifies_ref (r:rid) (s:Set.set aref) (s0:t) (s1:t) = 
  Heap.modifies s (Map.sel (heaps s0) r) (Map.sel (heaps s1) r)

open FStar.Set
let disjoint_regions (s1:set rid) (s2:set rid) = 
     forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> x <> y

val heapOf: #a:Type -> stacked a -> t -> Tot heap
let heapOf #a r s = Map.sel (heaps s) (frameOf r)

val asRef: #a:Type -> stacked a -> Tot (ref a)
let asRef #a r = as_ref (refOf r)

assume val stacked_to_ref_lemma_1: #a:Type -> x:stacked a -> y:stacked a -> Lemma
  (requires (x <> y))
  (ensures (asRef x <> asRef y))
  [SMTPat (x <> y)]

assume val stacked_to_ref_lemma_2: #a:Type -> x:stacked a -> y:stacked a -> Lemma
  (requires (x <> y))
  (ensures (refOf x =!= refOf y))
  
