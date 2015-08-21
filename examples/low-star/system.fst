(*--build-config
    options:--admit_fsi Set --admit_fsi Seq  --verify_module System --z3timeout 100;
    variables:LIB=../../lib PLATFORM=../../contrib/Platform/fst SST=../low-level;
  other-files:$LIB/classical.fst $LIB/ext.fst $LIB/set.fsi $LIB/seq.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/seqproperties.fst $LIB/list.fst $LIB/listTot.fst $SST/stack.fst $SST/listset.fst $LIB/ghost.fst $SST/located.fst $SST/lref.fst $SST/stackAndHeap.fst $SST/sst.fst $SST/sstCombinators.fst $SST/array.fsi $SST/array.fst buffer.fst
  --*)

module System

open Set
open Heap
open SST
open SSTCombinators
open StackAndHeap
open Lref
open Located
open SSTArray
open Ghost

open Buffer

(* File descriptor : id * index *)
type fd = nat * lref nat (* = ref nat * (idx:nat -> len:nat -> Tot byte) *)

(* Input stream to be read from a file descriptor *)
assume val readStreamT : 
  f:fd -> m:smem{liveRef (snd f) m} -> n:nat -> 
  Tot (s:(option (Seq.seq byte)){ is_Some s ==> Seq.length (Some.v s) <= n })

assume val readStream : 
  f:fd -> n:nat -> 
  PureMem (option (Seq.seq byte))
    (requires (fun m ->
    (liveRef (snd f) m)
     ))
    (ensures (fun m s ->
      (liveRef (snd f) m)
      /\ (s = readStreamT f m n)
     ))
       	   
(* System read function *)
assume val read :
  f:fd ->
  b:buffer -> 
  count:nat{ count <= b.length } -> 
  Mem nat
    (requires (fun m -> 
      (liveBuffer m b)
      /\ (liveRef (snd f) m)
     ))
    (ensures (fun m0 n m1 ->
      (liveBuffer m0 b) /\ (liveBuffer m1 b)
      /\ (liveRef (snd f) m0)
      /\ (is_Some (readStreamT f m0 count) ==> 
	    (n = Seq.length (Some.v (readStreamT f m0 count))
	    /\ (EqSub (sel m1 b.content) b.start_idx (Some.v (readStreamT f m0 count)) 0 n)))
      /\ (EqSubInv (sel m0 b.content) (sel m1 b.content) b.start_idx count)
     ))
    (eunion (eonly b.content) (only (snd f)))

(* Output stream to write to a file descriptor *)
assume val writeStreamT : 
  f:fd -> m:smem{liveRef (snd f) m} -> b:buffer{liveBuffer m b} -> 
  Tot (n:nat{n <= b.length})

assume val write :
  f:fd ->
  b:buffer -> 
  Mem nat
    (requires (fun m -> 
      (liveBuffer m b)
      /\ (liveRef (snd f) m)
     ))
    (ensures (fun m0 n m1 ->
      (liveBuffer m0 b) /\ (liveBuffer m1 b)
      /\ (liveRef (snd f) m0) /\ (liveRef (snd f) m1)
      /\ (n <= b.length /\ n >= 0) (* Issue : does not get it from the returned type *)
      /\ (is_Some (readStreamT f m1 n) /\ Seq.length (Some.v (readStreamT f m1 n)) = n)
      /\ (EqSub (Some.v (readStreamT f m1 n)) 0 (sel m0 b.content) b.start_idx n)
     ))
    (only (snd f))

val setOfList : #a:Type -> l:list a -> Tot (s:set a{ (forall (e:a). List.mem e l <==> Set.mem e s ) })
let rec setOfList l =
  match l with
  | [] -> Set.empty
  | hd::tl -> Set.union (Set.singleton hd) (setOfList tl)

val refSetFromBufferList : #a:Type -> list buffer -> Tot modset
let rec refSetFromBufferList l =
  match l with 
  | [] -> hide empty
  | hd::tl -> eunion (eonly hd.content) (refSetFromBufferList tl)

(* Specification of the system call readv *)
assume val readv : 
    f:fd -> 
    l:list buffer -> 
    Mem nat
      (requires (fun m -> 
	(AllDistinct m l)
	/\ (liveRef (snd f) m)
       ))
      (ensures (fun m0 n m1 ->
	(AllDistinct m0 l) /\ (AllDistinct m1 l)
	/\ (liveRef (snd f) m0)
	/\ (forall (b:buffer{List.mem b l}). glength b.content m0 = glength b.content m1)
	/\ (bufferListLength m0 l = bufferListLength m1 l)
	/\ (is_Some (readStreamT f m0 (bufferListLength m0 l)) ==> 
	      (n = Seq.length (Some.v (readStreamT f m0 (bufferListLength m0 l)))
	      /\ (Seq.Eq (Seq.slice (bufferListContent m1 l) 0 n) (Some.v (readStreamT f m0 (bufferListLength m0 l))))))
	/\ (forall (b:buffer{List.mem b l}) (i:nat{i < glength b.content m0}).
	      inBufferComplement m0 b i l ==> Seq.index (sel m0 b.content) i = Seq.index (sel m1 b.content) i)
       ))
      (eunion (refSetFromBufferList l) (only (snd f)))

(* Specification of the system call writev *)
assume val writev:
    f:fd ->
    l:list buffer ->
    Mem nat
      (requires (fun m -> 
	(AllDistinct m l)
	/\ (liveRef (snd f) m)
       ))
      (ensures (fun m0 n m1 ->
	(AllDistinct m0 l) /\ (AllDistinct m1 l)
	/\ (liveRef (snd f) m0) /\ (liveRef (snd f) m1)
	/\ (n <= bufferListLength m0 l /\ n >= 0)
	/\ (is_Some (readStreamT f m1 n) /\ Seq.length (Some.v (readStreamT f m1 n)) = n)
	/\ (Some.v (readStreamT f m1 n) = Seq.slice (bufferListContent m0 l) 0 n)
       ))    
      (only (snd f))
