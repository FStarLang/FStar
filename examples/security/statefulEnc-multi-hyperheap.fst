(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --admit_fsi Map;
    other-files:../../lib/ext.fst ../../lib/set.fsi ../../lib/heap.fst ../../lib/map.fsi ../../lib/hyperheap.fst ../../lib/seq.fsi
  --*)
(* A standalone experiment corresponding to building a stateful encryption on
   top of a stateless one ... along the lines of StatefulLHAE on top of AEAD_GCM *)

(* Still to do:
     Show that multiple instances do not overlap using footprints and dynamic frames
*)
module StatefulEncryption.MultiInstance.HyperHeap
open ST
open Set
open Seq
open HyperHeap

(* TODO: merge these next two functions and lemma/assumption with the seq library *)
val snoc : seq 'a -> 'a -> Tot (seq 'a)
let snoc s x = Seq.append s (Seq.create 1 x)

assume val emp: #a:Type -> Tot (seq a)
assume Length_emp: forall (a:Type).{:pattern (Seq.length (emp #a))} Seq.length (emp #a) = 0

//type Fresh (#a:Type) h0 (r:ref a) h1 = Heap.contains h1 r /\ not (Heap.contains h0 r)

type Let (#a:Type) (x:a) (body: (y:a{y=x} -> Type)) = body x

type plain
type cipher
type key

type basicEntry =
  | Entry : p:plain -> c:cipher -> basicEntry

type encryptor (i:rid) =
  | Enc : log:rref i (seq basicEntry) -> key -> encryptor i

type decryptor (i:rid) =
  | Dec : log:rref i (seq basicEntry) -> key -> decryptor i

type paired (#i:rid) (e:encryptor i) (d:decryptor i) = b2t (Enc.log e = Dec.log d)

type both =
  | Both : i:rid -> e:encryptor i -> d:decryptor i{paired e d} -> both

type Fresh (#a:Type) h0 (r:ref a) h1 = Heap.contains h1 r /\ not (Heap.contains h0 r)

val gen: unit -> ST both
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
      modifies Set.empty h0 h1
      /\ not (Map.contains h0 (Both.i b))
      /\ Map.contains h1 (Both.i b)
      /\ Heap.contains (Map.sel h1 (Both.i b))
                       (as_ref (Enc.log (Both.e b)))
      /\ sel h1 (Enc.log (Both.e b)) = emp))
let gen () =
  let key : key = magic () in
  let region = new_region () in
  let log = ralloc region emp in
  Both region (Enc log key) (Dec log key)

opaque logic type modifies (mods:set Heap.aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (Heap.concat h' (Heap.restrict h (complement mods))))

val enc : #i:rid -> e:encryptor i -> p:plain -> ST cipher
    (requires (fun h -> True))
    (ensures (fun h0 c h1 ->
                HyperHeap.modifies (Set.singleton i) h0 h1
                /\ modifies !{as_ref (Enc.log e)} (Map.sel h0 i) (Map.sel h1 i)
                /\ h1 = upd h0 (Enc.log e) (snoc (sel h0 (Enc.log e)) (Entry p c))))
let enc i e p =
    let c : cipher = magic () in
    op_ColonEquals (Enc.log e) (snoc (op_Bang (Enc.log e)) (Entry p c));
    c

assume val find_seq : #a:Type -> f:(a -> Tot bool) -> s:seq a
            -> Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)}) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})

opaque logic type trigger (i:nat) = True
val dec: #i:rid -> d:decryptor i -> c:cipher -> ST (option plain)
  (requires (fun h -> True))
  (ensures (fun h0 p h1 ->
              HyperHeap.modifies Set.empty h0 h1
              /\ (Let (sel h0 (Dec.log d))
                      (fun log ->
                          (is_None p ==> (forall (i:nat{i < Seq.length log}). Entry.c (Seq.index log i) <> c))
                          /\ (is_Some p ==> (exists (i:nat{i < Seq.length log}).{:pattern (trigger i)} Seq.index log i = Entry (Some.v p) c))))))
let dec i d c =
  let s = op_Bang (Dec.log d) in
  match find_seq (function Entry p c' -> c=c') s with
    | None -> None
    | Some j -> cut (trigger j); Some (Entry.p (Seq.index s j))

(* -------------------------------------------------------- *)
type statefulEntry =
  | StEntry : i:nat -> p:plain -> c:cipher -> statefulEntry

type st_encryptor (i:rid) =
  | StEnc : log: rref i (seq statefulEntry) -> ctr: rref i nat -> key:encryptor i -> st_encryptor i

type st_decryptor (i:rid) =
  | StDec : log: rref i (seq statefulEntry) -> ctr: rref i nat -> key:decryptor i -> st_decryptor i

type st_paired (#i:rid) (enc:st_encryptor i) (dec:st_decryptor i) =
      StEnc.log enc = StDec.log dec
      /\ paired (StEnc.key enc) (StDec.key dec)
      /\ as_ref (Enc.log (StEnc.key enc)) =!= as_ref (StEnc.log enc)
      /\ as_ref (StEnc.ctr enc) <> as_ref (StDec.ctr dec)
      /\ as_ref (StEnc.log enc) =!= as_ref (StEnc.ctr enc)                      //These last four are needed because seq is abstract
      /\ as_ref (StEnc.log enc) =!= as_ref (StDec.ctr dec)                      //...
      /\ as_ref (Enc.log (StEnc.key enc)) =!= as_ref (StEnc.ctr enc)            //...
      /\ as_ref (Enc.log (StEnc.key enc)) =!= as_ref (StDec.ctr dec)            //and so potentially equal to nat ... TODO: make seq a new type

type st_both =
  | STBoth : i:rid -> e:st_encryptor i -> d:st_decryptor i{st_paired e d} -> st_both

assume val with_seqn : nat -> plain -> Tot plain

type st_inv (#i:rid) (e:st_encryptor i) (d:st_decryptor i) (h:HyperHeap.t) =
  st_paired e d
  /\ Map.contains h i
  /\ Heap.contains (Map.sel h i) (as_ref (StEnc.log e))
  /\ Heap.contains (Map.sel h i) (as_ref (StEnc.ctr e))
  /\ Heap.contains (Map.sel h i) (as_ref (StDec.ctr d))
  /\ Heap.contains (Map.sel h i) (as_ref (Enc.log (StEnc.key e)))
  /\ Let (sel h (Enc.log (StEnc.key e))) (fun basic ->
     Let (sel h (StEnc.log e)) (fun st ->
     Let (sel h (StEnc.ctr e)) (fun w ->
     Let (sel h (StDec.ctr d)) (fun r ->
     Seq.length st = Seq.length basic
     /\ w = Seq.length st
     /\ r <= w
     /\ (forall (i:nat{i < Seq.length st}).
          Let (Seq.index st i) (fun st_en ->
            StEntry.i st_en = i
            /\ Seq.index basic i = Entry (with_seqn i (StEntry.p st_en)) (StEntry.c st_en)))))))

type st_enc_inv (#i:rid) (e:st_encryptor i) (h:HyperHeap.t) =
  exists (d:st_decryptor i). st_inv e d h

type st_dec_inv (#i:rid) (d:st_decryptor i) (h:HyperHeap.t) =
  exists (e:st_encryptor i). st_inv e d h

let refs_in_e (#i:rid) (e:st_encryptor i) = !{as_ref (StEnc.log e), as_ref (StEnc.ctr e), as_ref (Enc.log (StEnc.key e))}
let refs_in_d (#i:rid) (d:st_decryptor i) = !{as_ref (StDec.log d), as_ref (StDec.ctr d), as_ref (Dec.log (StDec.key d))}

val stateful_gen : unit -> ST st_both
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
              st_inv (STBoth.e b) (STBoth.d b) h1
              /\ HyperHeap.modifies Set.empty h0 h1
              /\ not (Map.contains h0 (STBoth.i b))
              /\ Map.contains h1 (STBoth.i b)))
let stateful_gen () =
  let Both i e d = gen () in
  let l = ralloc i emp in
  let w = ralloc i 0 in
  let r = ralloc i 0 in
  STBoth i (StEnc l w e) (StDec l r d)

val stateful_enc : #i:rid -> e:st_encryptor i -> p:plain -> ST cipher
  (requires (fun h -> st_enc_inv e h))
  (ensures (fun h0 c h1 ->
                    st_enc_inv e h1
                 /\ HyperHeap.modifies (Set.singleton i) h0 h1
                 /\ modifies (refs_in_e e) (Map.sel h0 i) (Map.sel h1 i)
                 /\ sel h1 (StEnc.log e) = snoc (sel h0 (StEnc.log e)) (StEntry (sel h0 (StEnc.ctr e)) p c)))
let stateful_enc i e p =
  let i = op_Bang (StEnc.ctr e) in
  let ip = with_seqn i p in
  let c = enc (StEnc.key e) ip in
  op_ColonEquals (StEnc.log e) (snoc (op_Bang (StEnc.log e)) (StEntry i p c));
  op_ColonEquals (StEnc.ctr e) (i + 1);
  c

val stateful_dec: #i:rid -> ad:nat -> d:st_decryptor i -> c:cipher -> ST (option plain)
  (requires (fun h -> st_dec_inv d h))
  (ensures (fun h0 p h1 ->
                st_dec_inv d h0
                /\ st_dec_inv d h1
                /\ HyperHeap.modifies (Set.singleton i) h0 h1
                /\ modifies !{as_ref (StDec.ctr d)} (Map.sel h0 i) (Map.sel h1 i)
                /\ Let (sel h0 (StDec.ctr d)) (fun (r:nat{r=sel h0 (StDec.ctr d)}) ->
                   Let (sel h0 (StDec.log d)) (fun (log:seq statefulEntry{log=sel h0 (StDec.log d)}) ->
                    (is_None p ==> (r = Seq.length log                     //nothing encrypted yet
                                    || StEntry.c (Seq.index log r) <> c    //bogus cipher
                                    || r <> ad))                           //reading at the wrong postition
                   /\ (is_Some p ==>
                          ((sel h1 (StDec.ctr d) = r + 1)
                           /\ StEntry.p (Seq.index log r) = Some.v p))))))
let stateful_dec i ad d c =
  match dec (StDec.key d) c with
    | None -> None
    | Some p ->
      let i = op_Bang (StDec.ctr d) in
      let l = op_Bang (StDec.log d) in
      if i < Seq.length l
      then let StEntry _ q _ = Seq.index l i in
           if i = ad
           then (op_ColonEquals (StDec.ctr d) (i + 1); Some q)
           else None
      else None


val test_st_frame : #i:rid -> #j:rid{i<>j}
                   -> s1:st_both{STBoth.i s1 = i}
                   -> s2:st_both{STBoth.i s2 = j}
                   -> ST unit
  (requires (fun h ->
                 st_inv (STBoth.e s1) (STBoth.d s1) h
              /\ st_inv (STBoth.e s2) (STBoth.d s2) h
              /\ sel h (StEnc.ctr (STBoth.e s1)) = sel h (StDec.ctr (STBoth.d s1))
              // /\ Heap.sel h (StEnc.ctr (STI.e s2)) = Heap.sel h (StDec.ctr (STI.d s2))
              ))
  (ensures (fun h0 _ h1 ->
                 st_inv (STBoth.e s1) (STBoth.d s1) h1
              /\ st_inv (STBoth.e s2) (STBoth.d s2) h1
              /\ HyperHeap.modifies (Set.union (Set.singleton i) (Set.singleton j)) h0 h1))
// note that we do not require new encryptor/decryptors,
// just that those in s1 are in sync, so that decryption cancels encryption
assume val mk_plain : unit -> ST plain (requires (fun h -> True)) (ensures (fun h0 x h1 -> h0=h1))
let test_st_frame i j s1 s2 =
  let p = mk_plain () in
  let q = mk_plain () in
  let g = stateful_gen () in
  // let s3 = stateful_gen() // also type-breaking; yes, because this modifies fp, basic_fp
  let ctr = op_Bang (StEnc.ctr (STBoth.e s1)) in
  let c0 = stateful_enc (STBoth.e s1) p in
  let c1 = stateful_enc (STBoth.e s1) q in
  let c2 = stateful_enc (STBoth.e s2) p in
  // let oX = stateful_dec (STBoth.d s1) c2 in // might succeed
  let o0 = stateful_dec (ctr) (STBoth.d s1) c0 in
  let o1 = stateful_dec (ctr + 1) (STBoth.d s1) c1 in
  assert (Some.v o0 = p);
  assert (Some.v o1 = q)
