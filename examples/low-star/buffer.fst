(*--build-config
    options:--admit_fsi Set --admit_fsi Seq  --verify_module Buffer --z3timeout 10;
    variables:LIB=../../lib PLATFORM=../../contrib/Platform/fst SST=../low-level;
  other-files:$LIB/classical.fst $LIB/ext.fst $LIB/set.fsi $LIB/seq.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/seqproperties.fst $LIB/list.fst $LIB/listTot.fst $LIB/listproperties.fst $SST/stack.fst $SST/listset.fst $LIB/ghost.fst $SST/located.fst $SST/lref.fst $SST/stackAndHeap.fst $SST/sst.fst $SST/sstCombinators.fst $SST/array.fsi $SST/array.fst
  --*)

module Buffer

open Set
open Heap
open SST
open SSTCombinators
open StackAndHeap
open Lref
open Located
open SSTArray
open Ghost
open Seq

(* From arrayAlgos.fst, useful to specifications *)
val liveArr : #a:Type -> smem -> sstarray a -> GTot bool
let liveArr m v =
  liveRef (reveal (asRef v)) m

val eonly :  #a:Type -> sstarray a -> Tot modset
let eonly s = (eonly (asRef s))

val sel : #a:Type -> m:smem -> v:(sstarray a){liveArr m v} -> GTot (Seq.seq a)
let sel m v = loopkupRef (reveal (asRef v)) m

val glength : #a:Type -> v:(sstarray a) -> m:smem{liveArr m v} -> GTot nat
let glength v m = Seq.length (sel m v)

(* Redefining localy some of the functions from Platform.Bytes 
 * to make it stateful *)
type byte = uint8

(*
type bytes = sstarray byte
type lbytes (#m:smem) (n:nat) = 
  b:bytes{ liveArr m b /\ Seq.length (loopkupRef (reveal (asRef b)) m) = n}
*)

type buffer = 
  { 
    content:sstarray byte;
    start_idx:nat;
    length:nat;
  }

(* Equality predicates for a sub part of seq *)
type EqSub (#a:Type) (s:Seq.seq a) (si:nat) (t:Seq.seq a) (ti:nat) (len:nat) =
  Seq.length s >= si + len /\ Seq.length t >= ti+len 
  /\ (forall (i:nat{i<len}). index s (i+si) = index t (i+ti))

assume val eqSub : #a:Type -> s:Seq.seq a -> si:nat -> t:Seq.seq a -> ti:nat -> len:nat ->
	 GTot (b:bool{ b <==> EqSub s si t ti len})

(* Equality predicates for a sub part of seq *)
type EqSubInv (#a:Type) (s:Seq.seq a) (t:Seq.seq a) (si:nat) (len:nat) =
  Seq.length s >= si + len /\ Seq.length t = Seq.length s 
  /\ (forall (i:nat{ (i < si \/ i >= len) /\ i < Seq.length s}). index s i = index t i)

val liveBuffer : 
  m:smem -> b:buffer -> 
  GTot (r:bool{ r = (liveArr m b.content && b.start_idx+b.length <= glength (b.content) m)})
let liveBuffer m b =
  liveArr m b.content
  && b.start_idx + b.length <= glength (b.content) m

type Distinct (m:smem) (b1:buffer) (b2:buffer) =
  (liveBuffer m b1) /\ (liveBuffer m b2)
  /\ (b1.content = b2.content ==> 
      (b1.start_idx <= b2.start_idx + b2.length 
	 \/ b2.start_idx <= b1.start_idx + b1.length))
	
type AllDistinct (m:smem) (l:list buffer) =
  (forall (e:buffer{ List.mem e l}). liveBuffer m e)
  /\ (forall (e1:buffer{ List.mem e1 l}) (e2:buffer{List.mem e2 l}). Distinct m e1 e2)

val allDistinctLemma : m:smem -> l:list buffer{ is_Cons l } -> 
  Lemma
    (requires (AllDistinct m l))
    (ensures (AllDistinct m (List.Tot.tl l)))
let allDistinctLemma m l = ()

val bufferListContent : m:smem -> l:list buffer{AllDistinct m l} -> GTot (s:seq byte)
let rec bufferListContent m l =
  match l with
  | [] -> Seq.createEmpty
  | b::tl -> 
     cut (True /\ liveBuffer m b);
     Seq.append (sel m b.content) (bufferListContent m tl)

val bufferListLength : m:smem -> l:list buffer{AllDistinct m l} -> GTot (n:nat{ n = Seq.length (bufferListContent  m l)})
let bufferListLength m l =
  Seq.length (bufferListContent m l)

val inBufferComplement : m:smem -> b:buffer{liveBuffer m b} -> i:nat -> l:list buffer -> GTot bool
let rec inBufferComplement m b i l =
  match l with
  | [] -> false
  | hd::tl ->
     (b.content = hd.content && i < glength hd.content m && (i >= hd.start_idx+hd.length || i < hd.start_idx))
     || inBufferComplement m b i tl

