(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --z3timeout 15 --max_fuel 1 --max_ifuel 1 --initial_ifuel 1 --max_ifuel 1;
    other-files:../../lib/ext.fst ../../lib/set.fsi ../../lib/heap.fst ../../lib/st.fst ../../lib/seq.fsi ../../lib/list.fst
  --*)
(* A standalone experiment corresponding to building stateful encryption on
   top of a stateless one ... along the lines of StatefulLHAE on top of AEAD_GCM *)
module StatefulEncryption.MultiInstance.Frame
open ST
open Set
open Heap
open Seq

(*------------- Some utilites --------- *)
(* TODO: merge these functions with the standard library *)
opaque logic type trigger (#a:Type) (x:a) = True

// snoc?
val snoc : seq 'a -> 'a -> Tot (seq 'a)
let snoc s x = Seq.append s (Seq.create 1 x)

assume val emp: #a:Type -> Tot (seq a)
assume Length_emp: forall (a:Type).{:pattern (Seq.length (emp #a))} Seq.length (emp #a) = 0

// we'll need variants passing i to f, and showing forall j. j < i ==> not f(Seq.index s j)
assume val find_seq : #a:Type -> f:(a -> Tot bool) -> s:seq a
            -> Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)}) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})

(* not quite typing...
// i is the next index to try
val find_seq' : #a:Type -> f:(a -> Tot bool) -> s:seq a ->
  i:nat { i <= Seq.length s /\ (forall (j:nat{j<i}). not (f (Seq.index s j))) } ->
  Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)} /\ (forall (j:nat{j<i}). not (f (Seq.index s j)))) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})
let rec find_seq' a f s i =
  if i = Seq.length s then None
  else if f (Seq.index s i) then Some i
  else find_seq' #a f s (i+1)
let find_seq a f s = find_seq' #a f s 0
*)

assume val seq_map: #a:Type -> #b:Type -> f:(a -> Tot b) -> s:seq a ->
  Tot (t:seq b { Seq.length t = Seq.length s /\ (forall (i:nat{i < Seq.length s}).(Seq.index t i = f (Seq.index s i))) })

// replacing the usual modifies clause?
// this does not preclude h' extending h with fresh refs
opaque logic type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (concat h' (restrict h (complement mods))))

type Fresh (#a:Type) h0 (r:ref a) h1 = Heap.contains h1 r /\ not (Heap.contains h0 r)

type Let (#a:Type) (x:a) (body: (y:a{y=x} -> Type)) = body x

(* ------------------------------------------------------------ *)
(* Start with a basic possibly-stateful encryption functionality *)

(* Some placeholder functions to build plain/cipher/key *)

type key
// we need something possibly stateful, accounting for random sampling & pairwise distinct keys
// similarly we should be able to instantiate the scheme to an instance that holds/updates refs in key

// assume val gen0: unit -> Tot key
assume val gen0: unit -> St key (fun h -> True) (fun h0 k h1 -> modifies !{} h0 h1)

type plain
assume val mk_plain: unit -> St plain (fun h -> True) (fun h0 k h1 -> modifies !{} h0 h1)

type ad = nat // additional data, just integers for simplicity

type cipher
assume val enc0: s:seq cipher (* ghost *) -> St cipher
  (fun h -> True)
  (fun h0 c h1 -> modifies !{} h0 h1
               /\ find_seq (fun c' -> c=c') s = None)

// to guarantees that decryption is a stateful inverse of encryption (a good sanity check),
// the invariant on entries should state that the ciphers are pairwise distinct.
// we may also have a refinement guaranteeing that decryption of that ciphertext yields that plaintext.

type basicEntry =
  | Entry : i:ad -> c:cipher -> p:plain -> basicEntry

type encryptor =
  | Enc : log:ref (seq basicEntry) -> key -> encryptor

type decryptor =
  | Dec : log:ref (seq basicEntry) -> key -> decryptor

type paired (e:encryptor) (d:decryptor) = b2t (Enc.log e = Dec.log d)

(* A basic instance *)
type bi =
  | BI : e:encryptor -> d:decryptor{paired e d} -> bi

// new concrete syntax for sets of (a & x:a) ?
let bi_refs (BI e d) = !{Enc.log e}

type distinct_bi (b1:bi) (b2:bi) =
  Set.Equal (Set.intersect (bi_refs b1) (bi_refs b2)) !{}

type pairwise_distinct (s:list bi) =
  forall b1 b2. List.mem b1 s /\ List.mem b2 s ==> (b1 = b2 \/ distinct_bi b1 b2)

(* basic_fp: the footprint of the basic encryption functionality.
             maintains all basic instances, bi
*)
let basic_fp : ref (s:list bi{pairwise_distinct s}) = ref []

// somewhat generic
// could we put the separation from basic_fp above instead?
// could we show that those refs are separated from others?
type basic_fp_inv (h:heap) =
  Heap.contains h basic_fp
  /\ (forall bi.
        List.mem bi (Heap.sel h basic_fp)
         ==> (forall (a:Type) (r:ref a).
                Set.mem (Ref r) (bi_refs bi)
                ==> Heap.contains h r /\ r =!= basic_fp))

val gen: unit -> St bi
  (requires (basic_fp_inv))
  (ensures (fun h0 b h1 ->
      modifies !{basic_fp} h0 h1
      /\ basic_fp_inv h1
      /\ Heap.sel h1 basic_fp = b::Heap.sel h0 basic_fp
      /\ Let (Enc.log (BI.e b)) (fun log ->
         Fresh h0 log h1
         /\ Heap.sel h1 log = emp)))
let gen () =
  let key = gen0 () in
  let log = ref emp in
  let bi = BI (Enc log key) (Dec log key) in
  basic_fp := bi::!basic_fp; //ghost
  bi

type in_basic_fp bi h =
  basic_fp_inv h /\
  b2t(List.mem bi (Heap.sel h basic_fp))

type enc_in_basic_fp (e:encryptor) (h:heap) = exists d. paired e d /\ in_basic_fp (BI e d) h
type dec_in_basic_fp (d:decryptor) (h:heap) = exists e. paired e d /\ in_basic_fp (BI e d) h

val enc : e:encryptor -> i:ad -> p:plain -> St cipher
    (requires (fun h -> enc_in_basic_fp e h))
    (ensures (fun h0 c h1 ->
                modifies !{Enc.log e} h0 h1
                /\ enc_in_basic_fp e h1
                // /\ Heap.contains h1 (Enc.log e) // could we get it from the precondition?
                /\ Heap.sel h1 (Enc.log e) = snoc (Heap.sel h0 (Enc.log e)) (Entry i c p)))
let enc e i p =
  // failing: let s = seq_map #basicEntry #cipher (fun (e:basicEntry) -> Entry.c e) !(Enc.log e) in
  let c = enc0 emp in
  Enc.log e := snoc !(Enc.log e) (Entry i c p);
  c

let basicMatch i c (Entry i' c' p) = i = i' && c = c'

// cryptographically, this assumes both INT-CTXT and IND-CPA (except for distinct ciphers)
val dec: d:decryptor -> a:ad -> c:cipher -> St (option plain)
  (requires (fun h -> dec_in_basic_fp d h))
  (ensures (fun h0 o h1 ->
              modifies !{} h0 h1
              /\ dec_in_basic_fp d h1
              /\ (Let (Heap.sel h0 (Dec.log d))
                      (fun log ->
                          (is_None o <==> (forall (i:nat{i < Seq.length log}).{:pattern (trigger i)} trigger i /\ ~(basicMatch a c (Seq.index log i))))
                          /\ (is_Some o ==> (exists (i:nat{i < Seq.length log}).{:pattern (trigger i)} trigger i /\ basicMatch a c (Seq.index log i) /\ Entry.p (Seq.index log i) = Some.v o))))))
let dec d a c =
  let s = !(Dec.log d) in
  match find_seq (basicMatch a c) s with
    | None -> None
    | Some i ->
      cut (trigger i);
      Some (Entry.p (Seq.index s i))

val test_basic_frame : b1:bi -> b2:bi{distinct_bi b1 b2} -> St unit
    (requires (fun h ->
                       in_basic_fp b1 h
                    /\ in_basic_fp b2 h
                    /\ Heap.sel h (Enc.log (BI.e b1)) = emp
                    /\ Heap.sel h (Enc.log (BI.e b2)) = emp))
    (ensures (fun h0 _ h1 ->
                basic_fp_inv h1
                /\ modifies (Set.union (bi_refs b1) (bi_refs b2)) h0 h1))
(* A test of multiple basic instances:
     proves that use of one instance doesn't mess with another
*)
let test_basic_frame b1 b2 =
  // let b3 = gen() in // this breaks typing; why?
  let p = mk_plain () in
  let q = mk_plain () in
  let c0 = enc (BI.e b1) 0 p in
  let c1 = enc (BI.e b1) 1 q in
  let c2 = enc (BI.e b2) 0 q in
  let o0 = dec (BI.d b1) 0 c0 in
  let o2 = dec (BI.d b2) 0 c2 in
  let oX = dec (BI.d b1) 2 c0 in // this fails with 1, as we might have c0=c1
  cut (trigger 0); // what does this achieve?
  assert (Some.v o0 = p);
  assert (Some.v o2 = q);
  assert (oX = None)

(* -------------------------------------------------------- *)
(* This is the analog of StatefulLHAE on top of AEAD_GCM *)
type statefulEntry =
  | StEntry : c:cipher -> p:plain -> statefulEntry

// we used to have a copy of i inside each entry; now gone
// as above, we could use a stronger invariant

type st_encryptor =
  | StEnc : log: ref (seq statefulEntry) -> ctr: ref nat -> key:encryptor -> st_encryptor

type st_decryptor =
  | StDec : log: ref (seq statefulEntry) -> ctr: ref nat -> key:decryptor -> st_decryptor

type st_paired (enc:st_encryptor) (dec:st_decryptor) =
      StEnc.log enc = StDec.log dec
      /\ paired (StEnc.key enc) (StDec.key dec)
      /\ Enc.log (StEnc.key enc) =!= StEnc.log enc
      /\ StEnc.ctr enc <> StDec.ctr dec
      /\ StEnc.log enc =!= StEnc.ctr enc                    //These last four are needed because seq is abstract
      /\ StEnc.log enc =!= StDec.ctr dec                    //...
      /\ Enc.log (StEnc.key enc) =!= StEnc.ctr enc          //...
      /\ Enc.log (StEnc.key enc) =!= StDec.ctr dec          //and so potentially equal to nat ... TODO: make seq a new type

(* a stateful instance *)
type sti =
  | STI : e:st_encryptor -> d:st_decryptor{st_paired e d} -> sti

// this is simplified from AEAD (usually not encrypted)

(* The invariant of a single instance *)
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
      /\ w = Seq.length st   //write counter is at the end of the log
      /\ r <= w              //read counter is before it
      /\ (forall (i:nat{i < Seq.length st}).
          Let (Seq.index st i) (fun st_en ->
            b2t (Seq.index basic i = Entry i (StEntry.c st_en) (StEntry.p st_en) )))))))

type st_enc_inv (e:st_encryptor) (h:heap) =
  exists (d:st_decryptor). st_paired e d /\ st_inv e d h

type st_dec_inv (d:st_decryptor) (h:heap) =
  exists (e:st_encryptor). st_paired e d /\ st_inv e d h

let sti_refs (STI e d) =
  Set.union !{StEnc.log e, StEnc.ctr e, StDec.ctr d}
            (bi_refs (BI (StEnc.key e) (StDec.key d)))

type distinct_sti (s1:sti) (s2:sti) =
  Set.Equal (Set.intersect (sti_refs s1) (sti_refs s2)) Set.empty

(* The footprint gathers all stateful instances *)
let st_fp : ref (list sti) = ref []
type st_fp_inv (h:heap) =
   basic_fp_inv h              //the basic encryption invariant
   /\ Heap.contains h st_fp
   /\ basic_fp =!= st_fp       //two footprints are anti-aliased
   /\ (forall s1.
          List.mem s1 (Heap.sel h st_fp)
          ==> (forall s2. List.mem s2 (Heap.sel h st_fp) ==> s1 = s2 \/ distinct_sti s1 s2) //pairwise distinct
               /\ in_basic_fp (BI (StEnc.key (STI.e s1)) (StDec.key (STI.d s1))) h //the key is in the basic invariant
               /\ st_inv (STI.e s1) (STI.d s1) h //and in the st invariant
               /\ (forall (a:Type) (r:ref a).
                    Set.mem (Ref r) (sti_refs s1)
                    ==> Heap.contains h r        //every ref is in the heap
                        /\ r =!= basic_fp        //and doesn't alias the footprints
                        /\ r =!= st_fp))

let refs_in_e (e:st_encryptor) = !{StEnc.log e, StEnc.ctr e, Enc.log (StEnc.key e)}
let refs_in_d (d:st_decryptor) = !{StDec.log d, StDec.ctr d, Dec.log (StDec.key d)}

val stateful_gen : unit -> St sti
  (requires (st_fp_inv))
  (ensures (fun h0 b h1 ->
              st_fp_inv h1
              /\ Heap.sel h1 st_fp = b::Heap.sel h0 st_fp
              /\ modifies !{basic_fp, st_fp} h0 h1
              /\ (forall (a:Type) (r:ref a). Set.mem (Ref r) (sti_refs b)
                    ==> Fresh h0 r h1)))
let stateful_gen () =
  let BI e d = gen () in
  let l = ref emp in
  let w = ref 0 in
  let r = ref 0 in
  let sti = STI (StEnc l w e) (StDec l r d) in
  st_fp := sti :: !st_fp; //ghost
  sti

type in_st_fp sti h =
  st_fp_inv h /\
  b2t( List.mem sti (Heap.sel h st_fp))

type enc_in_st_fp (e:st_encryptor) (h:heap) = exists d. st_paired e d /\ in_st_fp (STI e d) h
type dec_in_st_fp (d:st_decryptor) (h:heap) = exists e. st_paired e d /\ in_st_fp (STI e d) h

val stateful_enc : e:st_encryptor -> p:plain -> St cipher
  (requires (fun h -> enc_in_st_fp e h))
  (ensures (fun h0 c h1 ->
                    enc_in_st_fp e h1
                 /\ modifies (refs_in_e e) h0 h1
                 /\ Heap.sel h1 (StEnc.log e) //exactly plain added to the end of the log
                     = snoc (Heap.sel h0 (StEnc.log e)) (StEntry c p)))
let stateful_enc (StEnc log ctr e) p =
  let c = enc e !ctr p in
  log := snoc !log (StEntry c p);
  ctr := !ctr + 1;
  c

val stateful_dec: d:st_decryptor -> c:cipher -> St (option plain)
  (requires (fun h -> dec_in_st_fp d h))
  (ensures (fun h0 p h1 ->
                   dec_in_st_fp d h0 //repeating pre
                /\ dec_in_st_fp d h1
                /\ modifies !{StDec.ctr d} h0 h1
                /\ Let (Heap.sel h0 (StDec.ctr d)) (fun (r:nat{r=Heap.sel h0 (StDec.ctr d)}) ->
                   Let (Heap.sel h0 (StDec.log d)) (fun (log:seq statefulEntry{log=Heap.sel h0 (StDec.log d)}) ->
                    (is_None p ==> (r = Seq.length log                     //nothing encrypted yet
                                    || StEntry.c (Seq.index log r) <> c    //wrong cipher
                                    ) /\ Heap.sel h1 (StDec.ctr d) = r)
                   /\ (is_Some p ==>
                          ((Heap.sel h1 (StDec.ctr d) = r + 1)
                           /\ StEntry.p (Seq.index log r) = Some.v p))))))

// note that we do not increment the counter in case of decryption failure,
// thereby enabling retries
let stateful_dec (StDec _ ctr d) c =
  let i = !ctr in
  cut(trigger i); // what does it do?
  match dec d !ctr c with
    | None -> None
    | Some p -> ctr := !ctr + 1; Some p

// what does it do? related to transient failures?
#reset-options
val test_st_frame : s1:sti -> s2:sti{distinct_sti s1 s2} -> St unit
    (requires (fun h ->
                   in_st_fp s1 h
                /\ in_st_fp s2 h
                /\ Heap.sel h (StEnc.ctr (STI.e s1)) = Heap.sel h (StDec.ctr (STI.d s1))
             // /\ Heap.sel h (StEnc.ctr (STI.e s2)) = Heap.sel h (StDec.ctr (STI.d s2))
                    ))
    (ensures (fun h0 _ h1 ->
                   in_st_fp s1 h1
                /\ in_st_fp s2 h1
                /\ modifies (Set.union (sti_refs s1) (sti_refs s2)) h0 h1))
// note that we do not require new encryptor/decryptors,
// just that those in s1 are in sync, so that decryption cancels encryption

let test_st_frame s1 s2 =
  let p = mk_plain () in
  let q = mk_plain () in
  // let s3 = stateful_gen() // also type-breaking
  let c0 = stateful_enc (STI.e s1) p in
  let c1 = stateful_enc (STI.e s1) q in
  let c2 = stateful_enc (STI.e s2) p in
  // let oX = stateful_dec (STI.d s1) c2 in // might succeed
  let o0 = stateful_dec (STI.d s1) c0 in
  let o1 = stateful_dec (STI.d s1) c1 in
  assert (Some.v o0 = p);
  assert (Some.v o1 = q)
