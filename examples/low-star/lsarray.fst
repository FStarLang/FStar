(*--build-config
  options:--verify_module LSarray;
  variables:SST=../low-level;
  other-files:classical.fst ext.fst set.fsi set.fst seq.fsi seq.fst heap.fst st.fst all.fst seqproperties.fst list.fst listTot.fst listproperties.fst $SST/stack.fst $SST/listset.fst ghost.fst $SST/located.fst $SST/lref.fst $SST/regions.fst $SST/rst.fst
  --*)

(* Infix representation of arrays for the SST monad *)

module LSarray

open FStar.Set
open FStar.Heap
open RST
open Regions
open Lref
open Located
open FStar.Ghost
open Stack
open FStar.Seq

// Default value for a type, corresponds to a struct declaration in C
assume val instanceOf: a:Type -> Tot a

private type array (a:Type) = | Array: content:(lref (seq a)) -> start:nat -> length:nat -> array a

val asRef: #a:Type -> t:array a -> Tot (r:erased (lref (seq a)){r = hide (Array.content t) })
let asRef t = hide (Array.content t)

val length: #a:Type -> t:array a -> Tot (len:erased nat{ len = hide (Array.length t)})
let length t = hide (Array.length t)

val glength: #a:Type -> t:array a -> GTot (len:nat{ len = (Array.length t)})
let glength t = Array.length t

val index: #a:Type -> t:array a -> Tot (index:erased nat{ index = hide (Array.start t) })
let index t = hide (Array.start t)

val gindex: #a:Type -> t:array a -> GTot (index:nat{ index = (Array.start t)})
let gindex t = (Array.start t)

type live (#a:Type) (t:array a) (m:smem) = 
  (refIsLive (reveal (asRef t)) m)
  /\ (Seq.length (lookupRef (reveal (asRef t)) m) >= gindex t + glength t)

assume val create:
  a:Type -> len:nat -> 
  Mem (array a)
      (requires (fun m -> (isNonEmpty (st m)) ) )
      (ensures (fun m0 t m1 ->
		  (isNonEmpty (st m0))
		  /\ (not(contains (topRegion m0) (reveal (asRef t))))
		  /\ (m1 = allocateInTopR (reveal (asRef t)) (Seq.create len (instanceOf a)) m0)
		  (* (allocateInBlock (reveal (asRef t)) (topRegion m0) (topRegion m1) (Seq.create len (instanceOf a)))
		  /\ (regionLoc (reveal (asRef t)) = InStack (topstid m0))
		  /\ (topstid m0 = topstid m1)
		  /\ (mtail m0 = mtail m1) *)
		  ))
       (hide empty)
(*
let create 'a len = 
  let content = Seq.create len (instanceOf 'a) in
  Array (salloc content) 0 len
*)

assume val get: 
  #a:Type -> t:array a -> n:nat -> 
  PureMem a
    (requires (fun m -> 
		 (live t m)
		 /\ (n < glength t) ))
    (ensures (fun m v ->
		(live t m)
		/\ (n < glength t)
		/\ (v = Seq.index (lookupRef (reveal (asRef t)) m) (gindex t + n)) ))
(*
let get t n =
  let content = memread (Array.content t) in
  Seq.index content (Array.start t + n)
*)

assume val upd:
  #a:Type -> t:array a -> n:nat -> v:a -> 
  Mem unit
    (requires (fun m -> 
		 (live t m)
		 /\ (n < glength t)))
    (ensures (fun m0 _ m1 -> 
		(live t m1)
		/\ (live t m0)
		/\ (n < glength t)
		/\ (Seq.Eq  (lookupRef (reveal (asRef t)) m1) (Seq.upd (lookupRef (reveal (asRef t)) m0) n v))))
    (only (reveal (asRef t)))
(*
let upd t n v =
  let content = memread (Array.content t) in
  let upd_content = Seq.upd content n v in
  memwrite (Array.content t) upd_content
*)

assume val sub:
  #a:Type -> t:array a -> n:nat -> len:nat ->
  PureMem (array a)
    (requires (fun m -> 
		 (live t m)
		 /\ (n + len <= glength t)))
    (ensures (fun m t' -> 
		(live t m)
		/\ (n + len <= glength t)
		/\ (t' = Array (reveal (asRef t)) (gindex t + n) len)))
(*
let sub t n len =
  let content = Array.content t in
  Array content (Array.start t + n) len
*)
