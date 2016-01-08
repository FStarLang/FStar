(*--build-config
    options:--admit_fsi Set --admit_fsi Seq;
    other-files:../../lib/FStar.FunctionalExtensionality.fst ../../lib/FStar.Set.fsi ../../lib/FStar.Heap.fst ../../lib/FStar.ST.fst ../../lib/seq.fsi
  --*)
(* A standalone experiment corresponding to building a stateful encryption on
   top of a stateless one ... along the lines of StatefulLHAE on top of AEAD_GCM *)

(* Still to do:
     Show that multiple instances do not overlap using footprints and dynamic frames
*)
module StatefulEncryption.MultiInstance
open ST
open Set
open Heap
open Seq

(* TODO: merge these next two functions and lemma/assumption with the seq library *)
val snoc : seq 'a -> 'a -> Tot (seq 'a)
let snoc s x = Seq.append s (Seq.create 1 x)

assume val emp: #a:Type -> Tot (seq a)
assume Length_emp: forall (a:Type).{:pattern (Seq.length (emp #a))} Seq.length (emp #a) = 0

opaque logic type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (concat h' (restrict h (complement mods))))

type Fresh (#a:Type) h0 (r:ref a) h1 = Heap.contains h1 r /\ not (Heap.contains h0 r)

type Let (#a:Type) (x:a) (body: (y:a{y=x} -> Type)) = body x

type plain
type cipher
type key

type basicEntry =
  | Entry : p:plain -> c:cipher -> basicEntry

type encryptor =
  | Enc : log:ref (seq basicEntry) -> key -> encryptor

type decryptor =
  | Dec : log:ref (seq basicEntry) -> key -> decryptor

type paired (e:encryptor) (d:decryptor) = b2t (Enc.log e = Dec.log d)

type both = ed:(encryptor * decryptor){paired (fst ed) (snd ed)}

val gen: unit -> ST both
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
      modifies !{} h0 h1
      /\ Let (Enc.log (fst b)) (fun log ->
         Fresh h0 log h1
         /\ Heap.sel h1 log = emp)))
let gen () =
  let key : key = magic () in
  let log = ref emp in
  (Enc log key, Dec log key)

val enc : e:encryptor -> p:plain -> ST cipher
    (requires (fun h -> True))
    (ensures (fun h0 c h1 ->
                modifies !{Enc.log e} h0 h1
                /\ Heap.contains h1 (Enc.log e)
                /\ Heap.sel h1 (Enc.log e) = snoc (Heap.sel h0 (Enc.log e)) (Entry p c)))

let enc e p =
    let c : cipher = magic () in
    Enc.log e := snoc !(Enc.log e) (Entry p c);
    c

assume val find_seq : #a:Type -> f:(a -> Tot bool) -> s:seq a
            -> Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)}) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})

val dec: d:decryptor -> c:cipher -> ST (option plain)
  (requires (fun h -> True))
  (ensures (fun h0 p h1 ->
              modifies !{} h0 h1
              /\ (Let (Heap.sel h0 (Dec.log d))
                      (fun log ->
                          (is_None p ==> (forall (i:nat{i < Seq.length log}). Entry.c (Seq.index log i) <> c))
                          /\ (is_Some p ==> (exists (i:nat{i < Seq.length log}). Seq.index log i = Entry (Some.v p) c))))))
let dec d c =
  let s = !(Dec.log d) in
  match find_seq (function Entry p c' -> c=c') s with
    | None -> None
    | Some i -> Some (Entry.p (Seq.index s i))


(* -------------------------------------------------------- *)
type statefulEntry =
  | StEntry : i:nat -> p:plain -> c:cipher -> statefulEntry

type st_encryptor =
  | StEnc : log: ref (seq statefulEntry) -> ctr: ref nat -> key:encryptor -> st_encryptor

type st_decryptor =
  | StDec : log: ref (seq statefulEntry) -> ctr: ref nat -> key:decryptor -> st_decryptor


type st_paired (enc:st_encryptor) (dec:st_decryptor) =
      StEnc.log enc = StDec.log dec
      /\ paired (StEnc.key enc) (StDec.key dec)
      /\ (Enc.log (StEnc.key enc)) =!= StEnc.log enc
      /\ StEnc.ctr enc <> StDec.ctr dec
      /\ StEnc.log enc =!= StEnc.ctr enc                      //These last four are needed because seq is abstract
      /\ StEnc.log enc =!= StDec.ctr dec                      //...
      /\ (Enc.log (StEnc.key enc)) =!= StEnc.ctr enc            //...
      /\ (Enc.log (StEnc.key enc)) =!= StDec.ctr dec           //and so potentially equal to nat ... TODO: make seq a new type

type st_both = b:(st_encryptor * st_decryptor){st_paired (fst b) (snd b)}

assume val with_seqn : nat -> plain -> Tot plain

type st_inv (e:st_encryptor) (d:st_decryptor) (h:heap) =
  st_paired e d
  /\ Heap.contains h (StEnc.log e)
  /\ Heap.contains h (StEnc.ctr e)
  /\ Heap.contains h (StDec.ctr d)
  /\ Heap.contains h (Enc.log (StEnc.key e))
  /\ Let (Heap.sel h (Enc.log (StEnc.key e))) (fun basic ->
     Let (Heap.sel h (StEnc.log e)) (fun st ->
     Let (Heap.sel h (StEnc.ctr e)) (fun w ->
     Let (Heap.sel h (StDec.ctr d)) (fun r ->
     Seq.length st = Seq.length basic
     /\ w = Seq.length st
     /\ r <= w
     /\ (forall (i:nat{i < Seq.length st}).
          Let (Seq.index st i) (fun st_en ->
            StEntry.i st_en = i
            /\ Seq.index basic i = Entry (with_seqn i (StEntry.p st_en)) (StEntry.c st_en)))))))

type st_enc_inv (e:st_encryptor) (h:heap) =
  exists (d:st_decryptor). st_inv e d h

type st_dec_inv (d:st_decryptor) (h:heap) =
  exists (e:st_encryptor). st_inv e d h

let refs_in_e (e:st_encryptor) = !{StEnc.log e, StEnc.ctr e, Enc.log (StEnc.key e)}

let refs_in_d (d:st_decryptor) = !{StDec.log d, StDec.ctr d, Dec.log (StDec.key d)}

val stateful_gen : unit -> ST st_both
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
              st_inv (fst b) (snd b) h1
              /\ modifies !{} h0 h1
              /\ (forall (a:Type) (r:ref a). Set.mem (Ref r) (Set.union (refs_in_e (fst b)) (refs_in_d (snd b)))
                    ==> Fresh h0 r h1)))
let stateful_gen () =
  let e,d = gen () in
  let l = ref emp in
  let w = ref 0 in
  let r = ref 0 in
  (StEnc l w e, StDec l r d)

val stateful_enc : e:st_encryptor -> p:plain -> ST cipher
  (requires (fun h -> st_enc_inv e h))
  (ensures (fun h0 c h1 ->
                    st_enc_inv e h1
                 /\ modifies (refs_in_e e) h0 h1
                 /\ Heap.sel h1 (StEnc.log e) = snoc (Heap.sel h0 (StEnc.log e)) (StEntry (Heap.sel h0 (StEnc.ctr e)) p c)))

let stateful_enc e p =
  let i = !(StEnc.ctr e) in
  let ip = with_seqn i p in
  let c = enc (StEnc.key e) ip in
  StEnc.log e := snoc !(StEnc.log e) (StEntry i p c);
  StEnc.ctr e := i + 1;
  c

val stateful_dec: ad:nat -> d:st_decryptor -> c:cipher -> ST (option plain)
  (requires (fun h -> st_dec_inv d h))
  (ensures (fun h0 p h1 ->
                st_dec_inv d h0
                /\ st_dec_inv d h1
                /\ modifies !{StDec.ctr d} h0 h1
                /\ Let (Heap.sel h0 (StDec.ctr d)) (fun (r:nat{r=Heap.sel h0 (StDec.ctr d)}) ->
                   Let (Heap.sel h0 (StDec.log d)) (fun (log:seq statefulEntry{log=Heap.sel h0 (StDec.log d)}) ->
                    (is_None p ==> (r = Seq.length log                     //nothing encrypted yet
                                    || StEntry.c (Seq.index log r) <> c    //bogus cipher
                                    || r <> ad))                           //reading at the wrong postition
                   /\ (is_Some p ==>
                          ((Heap.sel h1 (StDec.ctr d) = r + 1)
                           /\ StEntry.p (Seq.index log r) = Some.v p))))))
let stateful_dec ad d c =
  match dec (StDec.key d) c with
    | None -> None
    | Some p ->
      let i = !(StDec.ctr d) in
      let l = !(StDec.log d) in
      if i < Seq.length l
      then let StEntry _ q _ = Seq.index l i in
           if i = ad
           then (StDec.ctr d := i + 1; Some q)
           else None
      else None
