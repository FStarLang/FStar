(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq;
    other-files:../../lib/FStar.FunctionalExtensionality.fst ../../lib/FStar.Set.fsi
    ../../lib/FStar.Heap.fst ../../lib/FStar.ST.fst ../../lib/FStar.All.fst
    ../../lib/seq.fsi
  --*)
module StatefulEncryption.SingleInstance
open FStar.ST
open FStar.Set
open FStar.Heap
open FStar.Seq

(* TODO: merge these next two functions and lemma/assumption with the seq library *)
val snoc : seq 'a -> 'a -> Tot (seq 'a)
let snoc s x = Seq.append s (Seq.create 1 x)

assume val emp: #a:Type -> Tot (seq a)
assume Length_emp: forall (a:Type).{:pattern (Seq.length (emp #a))} Seq.length (emp #a) = 0

type plain
type cipher
type key

type basicEntry =
  | Entry : p:plain -> c:cipher -> basicEntry

let basicLog : ref (seq basicEntry) = ref emp

val enc : key -> p:plain -> ST cipher
    (requires (fun h -> Heap.contains h basicLog))
    (ensures (fun h0 c h1 ->
                modifies (Set.singleton (Ref basicLog)) h0 h1
                /\ Heap.contains h1 basicLog
                /\ Heap.sel h1 basicLog = snoc (Heap.sel h0 basicLog) (Entry p c)))
let enc k p =
    let c = magic () in
    basicLog := snoc !basicLog (Entry p c);
    c


type Let (#a:Type) (x:a) (body: a -> Type) = body x

assume val find_seq : #a:Type -> f:(a -> Tot bool) -> s:seq a
            -> Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)}) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})

val dec: key -> c:cipher -> ST (option plain)
  (requires (fun h -> Heap.contains h basicLog))
  (ensures (fun h0 p h1 ->
              modifies Set.empty h0 h1
              /\ (Let (Heap.sel h0 basicLog)
                      (fun log ->
                          is_None p ==> (forall (i:nat{i < Seq.length log}). Entry.c (Seq.index log i) <> c)
                          /\ is_Some p ==> (exists (i:nat{i < Seq.length log}). Seq.index log i = Entry (Some.v p) c)))))
let dec key c =
  let s = !basicLog in
  match find_seq (function Entry p c' -> c=c') s with
    | None -> None
    | Some i -> Some (Entry.p (Seq.index s i))


(* -------------------------------------------------------- *)
type statefulEntry =
  | StEntry : i:nat -> p:plain -> c:cipher -> statefulEntry
let stLog : ref (seq statefulEntry) = ref emp
assume val with_seqn : nat -> plain -> Tot plain

type log_inv (h:heap) =
  Heap.contains h basicLog
  /\ Heap.contains h stLog
  /\ basicLog =!= stLog
  /\ Let (Heap.sel h basicLog) (fun basic ->
     Let (Heap.sel h stLog) (fun st ->
     Seq.length st = Seq.length basic
      /\ (forall (i:nat{i < Seq.length st}).
          Let (Seq.index st i) (fun st_en ->
            StEntry.i st_en = i
            /\ Seq.index basic i = Entry (with_seqn i (StEntry.p st_en)) (StEntry.c st_en)))))

val stateful_enc : key -> p:plain -> ST cipher
  (requires (fun h -> log_inv h))
  (ensures (fun h0 c h1 -> log_inv h1
                        /\ modifies (Set.union (Set.singleton (Ref basicLog)) (Set.singleton (Ref stLog))) h0 h1
                        /\ (exists (i:nat). Heap.sel h1 stLog = snoc (Heap.sel h0 stLog) (StEntry i p c))))
let stateful_enc key p =
  let i = Seq.length !stLog in
  let ip = with_seqn i p in
  let c = enc key ip in
  stLog := snoc !stLog (StEntry i p c);
  c
