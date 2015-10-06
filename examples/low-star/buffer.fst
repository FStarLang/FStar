(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --verify_module CBuffer --z3timeout 10;
    variables:PLATFORM=../../contrib/Platform/fst SST=../low-level;
  other-files:classical.fst ext.fst set.fsi seq.fsi heap.fst st.fst all.fst seqproperties.fst list.fst listTot.fst listproperties.fst $SST/stack.fst $SST/listset.fst ghost.fst $SST/located.fst $SST/lref.fst $SST/regions.fst $SST/rst.fst $SST/rstWhile.fst $SST/array.fsi $SST/array.fst
  --*)

module CBuffer

open FStar.Set
open FStar.Heap
open SST
open RSTWhile
open Regions
open Lref
open Located
open RSTArray
open FStar.Ghost
open FStar.Seq

(* From arrayAlgos.fst, useful to specifications *)
val liveArr : #a:Type -> smem -> sstarray a -> GTot bool
let liveArr m v =
  refIsLive (reveal (asRef v)) m

val eonly :  #a:Type -> sstarray a -> Tot modset
let eonly s = (eonly (asRef s))

val sel : #a:Type -> m:smem -> v:(sstarray a){liveArr m v} -> GTot (Seq.seq a)
let sel m v = lookupRef (reveal (asRef v)) m

val glength : #a:Type -> v:(sstarray a) -> m:smem{liveArr m v} -> GTot nat
let glength v m = Seq.length (sel m v)

(* Redefining localy some of the functions from Platform.Bytes
 * to make it stateful *)
type byte = uint8

(* TODO : length should be ghost *)
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
  GTot (r:bool{ r = (liveArr m b.content && b.start_idx+( b.length) <= glength (b.content) m)})
let liveBuffer m b =
  liveArr m b.content
  && b.start_idx + ( b.length) <= glength (b.content) m

// TODO : Change to disjoints
type Distinct (m:smem) (b1:buffer) (b2:buffer) =
  (liveBuffer m b1) /\ (liveBuffer m b2)
  /\ (b1.content = b2.content ==>
      (b1.start_idx <= b2.start_idx + ( b2.length)
	 \/ b2.start_idx <= b1.start_idx + ( b1.length)))


val nth_lemma:
  #a:Type -> l:list a -> n:nat{ n < List.length l } ->
  Lemma
    (requires (True))
    (ensures (is_Some (List.total_nth l n)))
    [SMTPat (List.total_nth l n)]
let rec nth_lemma l n =
  match n, l with
  | 0, _ -> ()
  | n, hd::tl -> nth_lemma tl (n-1)

val nth: #a:Type -> l:list a -> n:nat{ n < List.length l } -> Tot a
let rec nth l n = Some.v (List.total_nth l n)


(* TODO : change the name "Distinct" into "Disjoint" *)
type AllDistinct (m:smem) (l:list buffer) =
  (forall (e:buffer{ List.mem e l}). liveBuffer m e)
  /\ (forall (i:nat{i < List.length l}) (j:nat{j < List.length l /\ j <> i}).
        Distinct m (nth l i) (nth l j))

val nth_lemma2: #a:Type -> l:list a{ is_Cons l } -> n:pos{ n < List.length l } ->
  Lemma
    (requires (True))
    (ensures (nth l n = nth (List.Tot.tl l) (n-1)))
    [SMTPat (nth (List.Tot.tl l) (n-1))]
let nth_lemma2 l n = ()

val allDistinctLemma : m:smem -> l:list buffer{ is_Cons l } ->
  Lemma
    (requires (AllDistinct m l))
    (ensures (AllDistinct m (List.Tot.tl l)))
let rec allDistinctLemma m l =
  match l with
  | hd::[] -> ()
  | hd::tl -> admit ()


val bufferListContent : m:smem -> l:list buffer{ forall (e:buffer{ List.mem e l }). liveBuffer m e } -> GTot (s:seq byte) (decreases (List.length l))
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
     (b.content = hd.content
       && i < glength hd.content m
       && (i >= hd.start_idx+ ( hd.length) || i < hd.start_idx))
     || inBufferComplement m b i tl
