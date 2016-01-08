(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --verify_module System --z3timeout 10;
    variables:PLATFORM=../../contrib/Platform/fst SST=../low-level;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.SeqProperties.fst FStar.List.fst FStar.List.Tot.fst FStar.ListProperties.fst $SST/stack.fst $SST/listset.fst FStar.Ghost.fst $SST/located.fst $SST/lref.fst $SST/regions.fst $SST/rst.fst $SST/rstWhile.fst $SST/array.fsi $SST/array.fst buffer.fst
  --*)

module CSystem

open FStar.Set
open FStar.Heap
open RST
open RSTWhile
open Regions
open Lref
open Located
open RSTArray
open FStar.Ghost

open CBuffer

(* File descriptor : id * index *)
(* The file descriptor is currently represented as an int identifier
   and a reference to an integer representing the current index the file is
   at *)
(* TODO : fix the representation & map it with whatever is returned by
    the openfile function *)
type fd = nat * lref nat

(* Input stream to be read from a file descriptor *)
assume val readStreamT :
  f:fd -> m:smem{refIsLive (snd f) m} -> n:nat ->
  Tot (s:(option (Seq.seq byte)){ is_Some s ==> Seq.length (Some.v s) <= n })

assume val readStream :
  f:fd -> n:nat ->
  PureMem (option (Seq.seq byte))
    (requires (fun m ->
    (refIsLive (snd f) m)
     ))
    (ensures (fun m s ->
      (refIsLive (snd f) m)
      /\ (s = readStreamT f m n)
     ))

(* System read function *)
assume val read :
  f:fd ->
  b:buffer ->
  off:nat{ off >= b.start_idx} ->
  count:nat{ count <= b.length } ->
  Mem nat
    (requires (fun m ->
      (liveBuffer m b)
      /\ (refIsLive (snd f) m)
     ))
    (ensures (fun m0 n m1 ->
      (liveBuffer m0 b) /\ (liveBuffer m1 b)
      /\ (refIsLive (snd f) m0)
      /\ (is_Some (readStreamT f m0 count) ==>
	    (n = Seq.length (Some.v (readStreamT f m0 count))
	    /\ (EqSub (sel m1 b.content) off (Some.v (readStreamT f m0 count)) 0 n)))
      /\ (EqSubInv (sel m0 b.content) (sel m1 b.content) off count)
     ))
    (eunion (eonly b.content) (only (snd f)))

(* Output stream to write to a file descriptor *)
assume val writeStreamT :
  f:fd -> m:smem{refIsLive (snd f) m} -> b:buffer{liveBuffer m b} ->
  Tot (n:nat{n <= b.length})

assume val write :
  f:fd ->
  b:buffer ->
  Mem nat
    (requires (fun m ->
      (liveBuffer m b)
      /\ (refIsLive (snd f) m)
     ))
    (ensures (fun m0 n m1 ->
      (liveBuffer m0 b) /\ (liveBuffer m1 b)
      /\ (refIsLive (snd f) m0) /\ (refIsLive (snd f) m1)
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
(* TODO : write in terms of specs of read *)
assume val readv :
    f:fd ->
    l:list buffer ->
    Mem nat
      (requires (fun m ->
	           (AllDistinct m l)
	            /\ (refIsLive (snd f) m)
       ))
      (ensures (fun m0 n m1 ->
	         (AllDistinct m0 l) /\ (AllDistinct m1 l)
	          /\ (refIsLive (snd f) m0)
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
(* TODO : fix wrong speficification about the input being disjoints, it should
   not be the case for writev at least. *)
assume val writev:
    f:fd ->
    l:list buffer ->
    Mem nat
      (requires (fun m ->
	(AllDistinct m l)
	/\ (refIsLive (snd f) m)
       ))
      (ensures (fun m0 n m1 ->
	(AllDistinct m0 l) /\ (AllDistinct m1 l)
	/\ (refIsLive (snd f) m0) /\ (refIsLive (snd f) m1)
	/\ (n <= bufferListLength m0 l /\ n >= 0)
	/\ (is_Some (readStreamT f m1 n) /\ Seq.length (Some.v (readStreamT f m1 n)) = n)
	/\ (Some.v (readStreamT f m1 n) = Seq.slice (bufferListContent m0 l) 0 n)
       ))
      (only (snd f))

(* Returns a inet datagram socket e.g. socket(AF_INET, SOCK_DGRAM,0) *)
assume val get_inet_tcp_socket: unit ->
  PureMem fd
    (requires (fun m -> True))
    (ensures (fun m v -> True))

(* Accept connections on a socket, returns a socket connected to the client and
its address *)
assume val accept:
  f:fd ->
  PureMem (fd * string)
    (requires (fun m -> True))
    (ensures (fun m v -> True))

assume val bind: fd -> string -> int ->
  PureMem unit
    (requires (fun m -> True))
    (ensures (fun m v -> True))

assume val listen:
  fd -> int ->
  PureMem unit
    (requires (fun m -> True))
    (ensures (fun m v -> True))

type file_perm = int

type open_flag =
  | READ_ONLY
  | WRITE_ONLY
  | READ_WRITE
  | APPEND
  | CREATE

(* TODO : create a ghost "content" associated to the filedescriptor (and
   the memory state ?) *)
assume val openfile:
  string -> list open_flag -> file_perm ->
  PureMem fd
    (requires (fun m -> True))
    (ensures (fun m f -> refIsLive (snd f) m))
assume val close: fd -> Tot unit
