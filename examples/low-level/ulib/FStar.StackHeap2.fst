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

let t = (frame_ids:list rid{is_valid_stack frame_ids} & //the stack will contain at least 1 element; used to be contains at least 2 elements; is that intentional?
	 m:Map.t rid heap{forall i. List.Tot.contains i frame_ids ==> Map.contains m i})

let mem = t

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

(* s1 has a new frame on top of s0. JK: Because of maps monotonicity I believe it 
   guaranties the unicity of the new frame id, needs to be checked *)
let fresh_frame (s0:t) (s1:t) = 
  Cons.tl (frame_ids s1) = frame_ids s0 /\      //the new stack extends the old one by just one frame
  not (Map.contains (heaps s0) (top_frame_id s1)) /\ //this new frame is not anywhere in the old stack
  (heaps s1 = Map.upd (heaps s0) (top_frame_id s1) emp) //and the new frame's heap is empty

(* Specifies untouched heaps *)
let modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.equal (heaps m1) (Map.concat (heaps m1) (Map.restrict (Set.complement s) (heaps m0)))
  /\ Set.subset (Map.domain (heaps m0)) (Map.domain (heaps m1))

let modifies_top (m0:t) (m1:t) = frame_ids m0 = frame_ids m1 /\ modifies (Set.singleton (top_frame_id m1)) m0 m1

(* s01 is popped into s1 *)
let popped_stack (s0:t) (s1:t) =
  suffix_of [root] (frame_ids s0) /\  //again, seems vacuous
  Cons.tl (frame_ids s0) = frame_ids s1 /\ 
  modifies Set.empty s1 s0

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
  [SMTPat (modifies_ref (frameOf y) !{as_ref y} s0 s1); SMTPatT (x <> y)]
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
