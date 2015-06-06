(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --z3timeout 10 --max_fuel 1 --max_ifuel 1 --initial_ifuel 1 --max_ifuel 1;
    other-files:../../lib/ext.fst ../../lib/set.fsi ../../lib/heap.fst ../../lib/st.fst ../../lib/seq.fsi ../../lib/list.fst
  --*)
(* A standalone experiment corresponding to building a stateful encryption on
   top of a stateless one ... along the lines of StatefulLHAE on top of AEAD_GCM *)
module StatefulEncryption.MultiInstance.Frame
open ST
open Set
open Heap
open Seq

(*------------- Some utilites --------- *)
(* TODO: merge these functions with the standard library *)
opaque logic type trigger (#a:Type) (x:a) = True

val snoc : seq 'a -> 'a -> Tot (seq 'a)
let snoc s x = Seq.append s (Seq.create 1 x)

assume val emp: #a:Type -> Tot (seq a)
assume Length_emp: forall (a:Type).{:pattern (Seq.length (emp #a))} Seq.length (emp #a) = 0

assume val find_seq : #a:Type -> f:(a -> Tot bool) -> s:seq a
            -> Tot (o:option (i:nat{i < Seq.length s /\ f (Seq.index s i)}) { is_None o ==> (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i)))})

opaque logic type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (concat h' (restrict h (complement mods))))

type Fresh (#a:Type) h0 (r:ref a) h1 = Heap.contains h1 r /\ not (Heap.contains h0 r)

type Let (#a:Type) (x:a) (body: (y:a{y=x} -> Type)) = body x

(* ------------------------------------------------------------ *)
(* Some placeholder functions to build plain/cipher/key *)
type plain
assume val mk_plain: unit -> Tot plain
type cipher
assume val mk_cipher: unit -> Tot cipher
type key
assume val mk_key: unit -> Tot key

(* Start with a basic stateful encryption functionality *)
type basicEntry =
  | Entry : p:plain -> c:cipher -> basicEntry

type encryptor =
  | Enc : log:ref (seq basicEntry) -> key -> encryptor

type decryptor =
  | Dec : log:ref (seq basicEntry) -> key -> decryptor

type paired (e:encryptor) (d:decryptor) = b2t (Enc.log e = Dec.log d)

(* A basic instance *)
type bi =
  | BI : e:encryptor -> d:decryptor{paired e d} -> bi

let bi_refs (BI e d) = !{Enc.log e}

type distinct_bi (b1:bi) (b2:bi) =
  Set.Equal (Set.intersect (bi_refs b1) (bi_refs b2)) !{}

type pairwise_distinct (s:list bi) =
  forall b1 b2. List.mem b1 s /\ List.mem b2 s ==> (b1 = b2 \/ distinct_bi b1 b2)

(* basic_fp: the footprint of the basic encryption functionality.
             maintains all basic instances, bi
*)
let basic_fp : ref (s:list bi{pairwise_distinct s}) = ref []

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
  let key = mk_key () in
  let log = ref emp in
  let bi = BI (Enc log key) (Dec log key) in
  basic_fp := bi::!basic_fp; //ghost
  bi

type enc_in_basic_fp (e:encryptor) (h:heap) =
  exists d. paired e d /\ List.mem (BI e d) (Heap.sel h basic_fp)

type dec_in_basic_fp (d:decryptor) (h:heap) =
  exists e. paired e d /\ List.mem (BI e d) (Heap.sel h basic_fp)

let in_basic_fp bi h = List.mem bi (Heap.sel h basic_fp)

val enc : e:encryptor -> p:plain -> St cipher
    (requires (fun h -> basic_fp_inv h /\ enc_in_basic_fp e h))
    (ensures (fun h0 c h1 ->
                modifies !{Enc.log e} h0 h1
                /\ basic_fp_inv h1
                /\ Heap.contains h1 (Enc.log e)
                /\ Heap.sel h1 (Enc.log e) = snoc (Heap.sel h0 (Enc.log e)) (Entry p c)))
let enc e p =
  let c = mk_cipher () in
  Enc.log e := snoc !(Enc.log e) (Entry p c);
  c

val dec: d:decryptor -> c:cipher -> St (option plain)
  (requires (fun h -> basic_fp_inv h /\ dec_in_basic_fp d h))
  (ensures (fun h0 p h1 ->
              modifies !{} h0 h1
              /\ basic_fp_inv h1
              /\ (Let (Heap.sel h0 (Dec.log d))
                      (fun log ->
                          (is_None p <==> (forall (i:nat{i < Seq.length log}).{:pattern (trigger i)} trigger i /\ Entry.c (Seq.index log i) <> c))
                          /\ (is_Some p ==> (exists (i:nat{i < Seq.length log}).{:pattern (trigger i)} trigger i /\ Seq.index log i = Entry (Some.v p) c))))))
let dec d c =
  let s = !(Dec.log d) in
  match find_seq (function Entry p c' -> c=c') s with
    | None -> None
    | Some i ->
      cut (trigger i);
      Some (Entry.p (Seq.index s i))

val test_basic_frame : b1:bi -> b2:bi{distinct_bi b1 b2} -> St unit
    (requires (fun h -> basic_fp_inv h
                    /\ in_basic_fp b1 h
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
  let p1 = mk_plain () in
  let p2 = mk_plain () in
  let c1 = enc (BI.e b1) p1 in
  let c2 = enc (BI.e b2) p2 in
  let p1' = dec (BI.d b1) c1 in
  let p2' = dec (BI.d b2) c2 in
  cut (trigger 0);
  assert (is_Some p1' /\ Some.v p1' = p1);
  assert (is_Some p2' /\ Some.v p2' = p2)

(* -------------------------------------------------------- *)
(* This is the analog of StatefulLHAE on top of AEAD_GCM *)
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
      /\ (Enc.log (StEnc.key enc)) =!= StEnc.ctr enc          //...
      /\ (Enc.log (StEnc.key enc)) =!= StDec.ctr dec          //and so potentially equal to nat ... TODO: make seq a new type

(* a stateful instance *)
type sti =
  | STI : e:st_encryptor -> d:st_decryptor{st_paired e d} -> sti

(* an abstract function to add additional data to the plain text *)
assume val with_seqn : nat -> plain -> Tot plain

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
            StEntry.i st_en = i  //the log is in sync with the basic log, with the ith entry containing i as the additional data
            /\ Seq.index basic i = Entry (with_seqn i (StEntry.p st_en)) (StEntry.c st_en)))))))

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
          ==> (forall s2. List.mem s2 (Heap.sel h st_fp) ==> s1 = s2 \/ distinct_sti s1 s2)
               /\ in_basic_fp (BI (StEnc.key (STI.e s1)) (StDec.key (STI.d s1))) h
               /\ st_inv (STI.e s1) (STI.d s1) h
               /\ (forall (a:Type) (r:ref a).
                    Set.mem (Ref r) (sti_refs s1)
                    ==> Heap.contains h r
                        /\ r =!= basic_fp
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
#set-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let stateful_gen () =
  let BI e d = gen () in
  let l = ref emp in
  let w = ref 0 in
  let r = ref 0 in
  let sti = STI (StEnc l w e) (StDec l r d) in
  st_fp := sti :: !st_fp; //ghost
  sti

let in_st_fp sti h = List.mem sti (Heap.sel h st_fp)

type enc_in_st_fp (e:st_encryptor) (h:heap) =
  exists d. st_paired e d /\ in_st_fp (STI e d) h

type dec_in_st_fp (d:st_decryptor) (h:heap) =
  exists e. st_paired e d /\ List.mem (STI e d) (Heap.sel h st_fp)

val stateful_enc : e:st_encryptor -> p:plain -> St cipher
  (requires (fun h -> st_fp_inv h /\ enc_in_st_fp e h))
  (ensures (fun h0 c h1 ->
                  st_fp_inv h1
                 /\
                 modifies (refs_in_e e) h0 h1
                 /\ Heap.sel h1 (StEnc.log e) = snoc (Heap.sel h0 (StEnc.log e)) (StEntry (Heap.sel h0 (StEnc.ctr e)) p c)))
let stateful_enc e p =
  let h0 = get() in
  let i = !(StEnc.ctr e) in
  let ip = with_seqn i p in
  let c = enc (StEnc.key e) ip in
  StEnc.log e := snoc !(StEnc.log e) (StEntry i p c);
  StEnc.ctr e := i + 1;
  c


val stateful_dec: ad:nat -> d:st_decryptor -> c:cipher -> St (option plain)
  (requires (fun h -> st_fp_inv h /\ dec_in_st_fp d h))
  (ensures (fun h0 p h1 ->
                st_fp_inv h0
                /\ dec_in_st_fp d h0 //repeating pre
                /\ st_fp_inv h1
                /\ modifies !{StDec.ctr d} h0 h1
                /\ Let (Heap.sel h0 (StDec.ctr d)) (fun (r:nat{r=Heap.sel h0 (StDec.ctr d)}) ->
                   Let (Heap.sel h0 (StDec.log d)) (fun (log:seq statefulEntry{log=Heap.sel h0 (StDec.log d)}) ->
                    (is_None p ==> (r = Seq.length log                     //nothing encrypted yet
                                    || StEntry.c (Seq.index log r) <> c    //bogus cipher
                                    || r <> ad))                           //reading at the wrong postition
                   /\ (is_Some p ==>
                          ((Heap.sel h1 (StDec.ctr d) = r + 1)
                           /\ StEntry.p (Seq.index log r) = Some.v p))))))
#reset-options
//#set-options "--max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let stateful_dec ad d c =
  let i = !(StDec.ctr d) in
  cut(trigger i);
  match dec (StDec.key d) c with
    | None ->  None
    | Some p ->
      let l = !(StDec.log d) in
      if i < Seq.length l
      then let StEntry _ q _ = Seq.index l i in
           if i = ad
           then (StDec.ctr d := i + 1; Some q)
           else None
      else None
