(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --admit_fsi FStar.Map --max_ifuel 1 --initial_ifuel 1 --initial_fuel 0 --max_fuel 0 --z3timeout 10;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst seq.fsi
  --*)
(* A standalone experiment corresponding to building a stateful encryption on
   top of a stateless one ... along the lines of StatefulLHAE on top of AEAD_GCM *)
module StatefulEncryption.MultiInstance.HyperHeap

open FStar.ST
open FStar.Set
open FStar.Seq
open FStar.HyperHeap

(* TODO: merge these next two functions and lemma/assumption with the seq library *)
val snoc : seq 'a -> 'a -> Tot (seq 'a)
let snoc s x = Seq.append s (Seq.create 1 x)

assume val emp: #a:Type -> Tot (seq a)
assume Length_emp: forall (a:Type).{:pattern (Seq.length (emp #a))} Seq.length (emp #a) = 0
type Let (#a:Type) (x:a) (body: (y:a{y=x} -> Type)) = body x

type plain
type cipher
type key
type ad = nat
type basicEntry =
  | Entry : ad:ad -> c:cipher -> p:plain ->basicEntry

type encryptor (i:rid) =
  | Enc : log:rref i (seq basicEntry) -> key -> encryptor i

type decryptor (i:rid) =
  | Dec : log:rref i (seq basicEntry) -> key -> decryptor i

type paired (#i:rid) (e:encryptor i) (d:decryptor i) = b2t (Enc.log e = Dec.log d)

type both =
  | Both : i:rid -> e:encryptor i -> d:decryptor i{paired e d} -> both

val gen: r0:rid -> ST both
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
      HyperHeap.modifies Set.empty h0 h1
      /\ fresh_region (Both.i b) h0 h1
      /\ contains_ref (Enc.log (Both.e b)) h1
      /\ sel h1 (Enc.log (Both.e b)) = emp))
let gen r0 =
  let key : key = magic () in
  let region = new_region r0 in
  let log = ralloc region emp in
  Both region (Enc log key) (Dec log key)

assume val find_seq : #a:Type -> f:(a -> Tot bool) -> s:seq a
            -> Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)}) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})

assume val enc0: s:seq cipher (* ghost *)
           -> ST cipher
  (fun h -> True)
  (fun h0 c h1 -> h0=h1
               /\ find_seq (fun c' -> c=c') s = None)

val enc : #i:rid -> e:encryptor i -> ad:ad -> p:plain -> ST cipher
    (requires (fun h -> True))
    (ensures (fun h0 c h1 ->
                HyperHeap.modifies (Set.singleton i) h0 h1
                /\ Heap.modifies !{as_ref (Enc.log e)} (Map.sel h0 i) (Map.sel h1 i)
                /\ h1 = upd h0 (Enc.log e) (snoc (sel h0 (Enc.log e)) (Entry ad c p))))
let enc i e ad p =
  let c = enc0 emp in
  op_Colon_Equals (Enc.log e) (snoc (op_Bang (Enc.log e)) (Entry ad c p));
  c

let basicMatch i c (Entry i' c' p) = i = i' && c = c'
opaque logic type trigger (i:nat) = True
val dec: #i:rid -> d:decryptor i -> a:ad -> c:cipher -> ST (option plain)
  (requires (fun h -> True))
  (ensures (fun h0 o h1 ->
              HyperHeap.modifies Set.empty h0 h1
              /\ (Let (sel h0 (Dec.log d))
                      (fun log ->
                          (is_None o ==> (forall (i:nat{i < Seq.length log}).{:pattern (trigger i)}
                                            trigger i /\ ~(basicMatch a c (Seq.index log i))))
                          /\ (is_Some o ==> (exists (i:nat{i < Seq.length log}).{:pattern (trigger i)}
                                                  trigger i
                                                  /\ basicMatch a c (Seq.index log i)
                                                  /\ Entry.p (Seq.index log i) = Some.v o))))))
let dec i d a c =
  let s = op_Bang (Dec.log d) in
  match find_seq (basicMatch a c) s with
    | None -> None
    | Some j -> cut (trigger j); Some (Entry.p (Seq.index s j))

(* A test of multiple basic instances:
   proves that use of one instance doesn't mess with another
*)
val test_basic_frame : r0:rid -> b1:both -> b2:both{Both.i b1 <> Both.i b2} -> ST unit
    (requires (fun h -> Map.contains h (Both.i b1)
                        /\ Map.contains h (Both.i b2)
                        /\ sel h (Enc.log (Both.e b1)) = emp
                        /\ sel h (Enc.log (Both.e b2)) = emp))
    (ensures (fun h0 _ h1 ->
                  HyperHeap.modifies (Set.union (Set.singleton (Both.i b1))
                                                (Set.singleton (Both.i b2)))
                            h0 h1))
assume val mk_plain : unit -> ST plain (requires (fun h -> True)) (ensures (fun h0 x h1 -> h0=h1))
let test_basic_frame r0 b1 b2 =
 let b3 = gen r0 in
 let p = mk_plain () in
 let q = mk_plain () in
 let c0 = enc (Both.e b1) 0 p in
 let c1 = enc (Both.e b1) 1 q in
 let c2 = enc (Both.e b2) 0 q in
 let o0 = dec (Both.d b1) 0 c0 in
 let o2 = dec (Both.d b2) 0 c2 in
 let oX = dec (Both.d b1) 2 c0 in // this fails with 1, as we might have c0=c1
 cut (trigger 0);
 assert (Some.v o0 = p);
 assert (Some.v o2 = q);
 assert (oX = None)

(* -------------------------------------------------------- *)
type statefulEntry =
  | StEntry : c:cipher -> p:plain -> statefulEntry

type st_encryptor (i:rid) =
  | StEnc : log: rref i (seq statefulEntry) -> ctr: rref i nat -> key:encryptor i -> st_encryptor i

type st_decryptor (i:rid) =
  | StDec : log: rref i (seq statefulEntry) -> ctr: rref i nat -> key:decryptor i -> st_decryptor i

type st_paired (#i:rid) (enc:st_encryptor i) (dec:st_decryptor i) =
      StEnc.log enc = StDec.log dec
      /\ paired (StEnc.key enc) (StDec.key dec)
      /\ (Enc.log (StEnc.key enc)) =!= (StEnc.log enc)
      /\ (StEnc.ctr enc) <> (StDec.ctr dec)
      /\ (StEnc.log enc) =!= (StEnc.ctr enc)                      //These last four are needed because seq is abstract
      /\ (StEnc.log enc) =!= (StDec.ctr dec)                      //...
      /\ (Enc.log (StEnc.key enc)) =!= (StEnc.ctr enc)            //...
      /\ (Enc.log (StEnc.key enc)) =!= (StDec.ctr dec)            //and so potentially equal to nat ... TODO: make seq a new type

type sti =
  | STI : i:rid -> e:st_encryptor i -> d:st_decryptor i{st_paired e d} -> sti

type st_inv (#i:rid) (e:st_encryptor i) (d:st_decryptor i) (h:HyperHeap.t) =
  st_paired e d
  /\ Map.contains h i
  /\ contains_ref (StEnc.log e) h
  /\ contains_ref (StEnc.ctr e) h
  /\ contains_ref (StDec.ctr d) h
  /\ contains_ref (Enc.log (StEnc.key e)) h
  /\ Let (sel h (Enc.log (StEnc.key e))) (fun basic ->
     Let (sel h (StEnc.log e)) (fun st ->
     Let (sel h (StEnc.ctr e)) (fun w ->
     Let (sel h (StDec.ctr d)) (fun r ->
     Seq.length st = Seq.length basic
     /\ w = Seq.length st
     /\ r <= w
     /\ (forall (i:nat{i < Seq.length st}).
          Let (Seq.index st i) (fun st_en ->
              b2t (Seq.index basic i = Entry i (StEntry.c st_en) (StEntry.p st_en))))))))

type st_enc_inv (#i:rid) (e:st_encryptor i) (h:HyperHeap.t) =
  exists (d:st_decryptor i). st_inv e d h

type st_dec_inv (#i:rid) (d:st_decryptor i) (h:HyperHeap.t) =
  exists (e:st_encryptor i). st_inv e d h

let refs_in_e (#i:rid) (e:st_encryptor i) = !{as_ref (StEnc.log e), as_ref (StEnc.ctr e), as_ref (Enc.log (StEnc.key e))}
let refs_in_d (#i:rid) (d:st_decryptor i) = !{as_ref (StDec.log d), as_ref (StDec.ctr d), as_ref (Dec.log (StDec.key d))}

val stateful_gen : r0:rid -> ST sti
  (requires (fun h -> True))
  (ensures (fun h0 b h1 ->
              st_inv (STI.e b) (STI.d b) h1
              /\ HyperHeap.modifies Set.empty h0 h1
              /\ fresh_region (STI.i b) h0 h1))
let stateful_gen r0 =
  let Both i e d = gen r0 in
  let l = ralloc i emp in
  let w = ralloc i 0 in
  let r = ralloc i 0 in
  STI i (StEnc l w e) (StDec l r d)

val stateful_enc : #i:rid -> e:st_encryptor i -> p:plain -> ST cipher
  (requires (fun h -> st_enc_inv e h))
  (ensures (fun h0 c h1 ->
                    st_enc_inv e h1
                 /\ HyperHeap.modifies (Set.singleton i) h0 h1
                 /\ Heap.modifies (refs_in_e e) (Map.sel h0 i) (Map.sel h1 i)
                 /\ sel h1 (StEnc.log e) = snoc (sel h0 (StEnc.log e)) (StEntry c p)))
let stateful_enc i (StEnc log ctr e) p =
    let c = enc e (op_Bang ctr) p in
    op_Colon_Equals log (snoc (op_Bang log) (StEntry c p));
    op_Colon_Equals ctr (op_Bang ctr + 1);
    c

val stateful_dec: #i:rid -> d:st_decryptor i -> c:cipher -> ST (option plain)
  (requires (fun h -> st_dec_inv d h))
  (ensures (fun h0 p h1 ->
                st_dec_inv d h0    //repeating pre
                /\ st_dec_inv d h1
                /\ HyperHeap.modifies (Set.singleton i) h0 h1
                /\ Heap.modifies !{as_ref (StDec.ctr d)} (Map.sel h0 i) (Map.sel h1 i)
                /\ Let (sel h0 (StDec.ctr d)) (fun (r:nat{r=sel h0 (StDec.ctr d)}) ->
                   Let (sel h0 (StDec.log d)) (fun (log:seq statefulEntry{log=sel h0 (StDec.log d)}) ->
                    (is_None p ==> (r = Seq.length log                     //nothing encrypted yet
                                    || StEntry.c (Seq.index log r) <> c    //wrong cipher
                                    ) /\ sel h1 (StDec.ctr d) = r)
                   /\ (is_Some p ==>
                          ((sel h1 (StDec.ctr d) = r + 1)
                           /\ StEntry.p (Seq.index log r) = Some.v p))))))
// note that we do not increment the counter in case of decryption failure,
// thereby enabling retries
let stateful_dec _id (StDec _ ctr d) c =
  let i = op_Bang ctr in
  cut(trigger i);
  match dec d (op_Bang ctr) c with
    | None -> None
    | Some p -> op_Colon_Equals ctr (op_Bang ctr + 1); Some p


val test_st_frame :r0:rid 
                   -> s1:sti
                   -> s2:sti{STI.i s1 <> STI.i s2}
                   -> ST unit
  (requires (fun h ->
                 st_inv (STI.e s1) (STI.d s1) h
              /\ st_inv (STI.e s2) (STI.d s2) h
              /\ sel h (StEnc.ctr (STI.e s1)) = sel h (StDec.ctr (STI.d s1))
              // /\ Heap.sel h (StEnc.ctr (STI.e s2)) = Heap.sel h (StDec.ctr (STI.d s2))
              ))
  (ensures (fun h0 _ h1 ->
                 st_inv (STI.e s1) (STI.d s1) h1
              /\ st_inv (STI.e s2) (STI.d s2) h1
              /\ HyperHeap.modifies (Set.union (Set.singleton (STI.i s1)) (Set.singleton (STI.i s2))) h0 h1))

// note that we do not require new encryptor/decryptors,
// just that those in s1 are in sync, so that decryption cancels encryption
let test_st_frame r0 s1 s2 =
  let p = mk_plain () in
  let q = mk_plain () in
  let g = stateful_gen r0 in
  let ctr = op_Bang (StEnc.ctr (STI.e s1)) in
  let c0 = stateful_enc (STI.e s1) p in
  let c1 = stateful_enc (STI.e s1) q in
  let c2 = stateful_enc (STI.e s2) p in
  // let oX = stateful_dec (STI.d s1) c2 in // might succeed
  let o0 = stateful_dec (STI.d s1) c0 in
  let o1 = stateful_dec (STI.d s1) c1 in
  assert (Some.v o0 = p);
  assert (Some.v o1 = q)
