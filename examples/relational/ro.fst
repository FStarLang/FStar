(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/st2.fst $LIB/bytes.fst $LIB/list.fst
  --*)

module Ro

open Comp
open Heap
open List
open Bytes

type map (a:Type) (b:Type) = list (a * b)

let eta = 16

type key = b:bytes
type tag = b:bytes{length(b)=eta}

(* TODO? *)
(* an abstract relational predicate on correctly-generated entries *)
assume logic type safe_key (k0:key) (k1:key)
let safe_key_unique = assume (forall k0 k1 k1'.
                               (safe_key k0 k1 /\ safe_key k0 k1' ==> k1 = k1'))
let safe_key_unique' = assume (forall k0 k0' k1.
                               (safe_key k0 k1 /\ safe_key k0' k1 ==> k0 = k0'))
assume logic type safe (k0:key) (k1:key) (t0:tag) (t1:tag)

type alloc =
  | Hon: alloc
  | Adv: alloc (* a "ghost" field recording the first allocator for a given key *)

type log = map key (alloc * tag)

type state_hash =
  { bad: bool; (* set iff any allocation has failed, e.g. bumped into the other's table *)
    l:log }    (* the map ensures at most one entry per key *)


type Ok : log -> log -> Type =
  | Null: Ok [] []
  | ConsH: k0:key -> k1:key{safe_key k0 k1} -> t0:tag -> t1:tag{safe k0 k1 t0 t1}
           -> log0:log{is_None (assoc k0 log0)}
           -> log1:log{is_None (assoc k1 log1)}
           -> p: Ok log0 log1
           -> Ok ((k0,(Hon,t0))::log0) ((k1,(Hon,t1))::log1)
  | ConsA: k:key -> t:tag
           -> log0:log{is_None (assoc k log0)}
           -> log1:log{is_None (assoc k log1)}
           -> p: Ok log0 log1
           -> Ok ((k ,(Adv,t ))::log0) ((k, (Adv,t ))::log1)

assume val ok_as_proof : l0:log -> l1:log {Ok l0 l1} -> Tot (Ok l0 l1)
assume val ok_as_refinement : #l0:log -> #l1:log  -> p:Ok l0 l1 -> Tot (u:unit{Ok l0 l1})

val ok_consH : k0:key -> k1:key{safe_key k0 k1} -> t0:tag
              -> t1:tag{safe k0 k1 t0 t1}
              -> l0:log{is_None (assoc k0 l0)}
              -> l1:log{is_None (assoc k1 l1) /\ Ok l0 l1} ->
               Lemma (requires True)
                     (ensures Ok ((k0,(Hon,t0))::l0) ((k1,(Hon,t1))::l1))
                     [SMTPat (assoc k0 l0);SMTPat (assoc k1 l1)]
let ok_consH k0 k1 t0 t1 l0 l1 = ok_as_refinement(ConsH k0 k1 t0 t1 l0 l1 (ok_as_proof l0 l1))

val ok_consA : k:key -> t:tag -> l0:log{is_None(assoc k l0)}
               -> l1:log{is_None(assoc k l1) /\ Ok l0 l1}
               -> Lemma (requires True)
                        (ensures Ok ((k,(Adv,t))::l0) ((k,(Adv,t))::l1))
                        [SMTPat (assoc k l0);SMTPat (assoc k l1)]
let ok_consA k t l0 l1 = ok_as_refinement (ConsA k t l0 l1 (ok_as_proof l0 l1))

val ok_adv_eq' : l0:log -> l1:log -> p:Ok l0 l1 -> k:key
                -> Lemma
                   (requires True)
                   (ensures (forall t. assoc k l0 = Some(Adv, t) <==>
                                       assoc k l1 = Some(Adv, t)))
let rec ok_adv_eq' l0 l1 p k = match p with
        | Null -> ()
        | ConsH _ _ _ _ tl0 tl1 p' -> ok_adv_eq' tl0 tl1 p' k
        | ConsA _ _ tl0 tl1 p' -> ok_adv_eq' tl0 tl1 p' k


val ok_adv_eq : l0:log -> l1:log{Ok l0 l1} ->  k:key
                -> Lemma
                   (requires True)
                   (ensures (forall t. assoc k l0 = Some(Adv, t) <==>
                                       assoc k l1 = Some(Adv, t)))
                  [SMTPat (assoc k l0); SMTPat (assoc k l1)]
let ok_adv_eq l0 l1 k = ok_adv_eq' l0 l1 (ok_as_proof l0 l1) k


val ok_hon_safe' : k0:key -> k1:key -> l0:log -> l1:log -> p:Ok l0 l1
                -> Lemma
                   (requires (safe_key k0 k1))
                   (ensures ( (is_Some(assoc k0 l0) /\ is_Hon(fst (Some.v(assoc k0 l0)))) <==>
                               is_Some(assoc k1 l1) /\ is_Hon(fst (Some.v(assoc k1 l1)))))
let rec ok_hon_safe' k0 k1 l0 l1 p = match p with
        | Null -> ()
        | ConsH k0' k1' t01 t1' tl0 tl1 p' -> ok_hon_safe' k0 k1 tl0 tl1 p'
        | ConsA k' t' tl0 tl1 p' -> ok_hon_safe' k0 k1 tl0 tl1 p'

val ok_hon_safe: k0:key -> k1:key -> l0:log -> l1:log {p:Ok l0 l1}
                -> Lemma
                   (requires (safe_key k0 k1))
                   (ensures ( ((is_Some(assoc k0 l0) /\ is_Hon(fst (Some.v(assoc k0 l0)))) <==>
                               is_Some(assoc k1 l1) /\ is_Hon(fst (Some.v(assoc k1 l1))))))
                               [SMTPat (assoc k0 l0); SMTPat (assoc k1 l1)]
let ok_hon_safe k0 k1 l0 l1 = ok_hon_safe' k0 k1 l0 l1 (ok_as_proof l0 l1)


val ok_hon_safe2' : k0:key -> k1:key -> l0:log -> l1:log -> p:Ok l0 l1
                -> Lemma
                   (requires (safe_key k0 k1))
                   (ensures (is_Some(assoc k0 l0) /\ is_Some(assoc k1 l1) /\
                             is_Hon(fst(Some.v (assoc k0 l0))) /\
                             is_Hon(fst(Some.v (assoc k0 l0))) ==>
                               safe k0 k1 (snd(Some.v (assoc k0 l0))) (snd(Some.v (assoc k1 l1)))))
let rec ok_hon_safe2' k0 k1 l0 l1 p = match p with
        | Null -> ()
        | ConsH k0' k1' t01 t1' tl0 tl1 p' -> ok_hon_safe2' k0 k1 tl0 tl1 p'
        | ConsA k' t' tl0 tl1 p' -> ok_hon_safe2' k0 k1 tl0 tl1 p'


val ok_hon_safe2 : k0:key -> k1:key -> l0:log -> l1:log{Ok l0 l1}
                 -> Lemma
                    (requires (safe_key k0 k1))
                    (ensures (is_Some(assoc k0 l0) /\ is_Some(assoc k1 l1) /\
                              is_Hon(fst(Some.v (assoc k0 l0))) /\
                              is_Hon(fst(Some.v (assoc k0 l0))) ==>
                                safe k0 k1 (snd(Some.v (assoc k0 l0))) (snd(Some.v (assoc k1 l1)))))
                                [SMTPat (assoc k0 l0); SMTPat (assoc k1 l1)]
let ok_hon_safe2 k0 k1 l0 l1 = ok_hon_safe2' k0 k1 l0 l1 (ok_as_proof l0 l1)

type goodstate_hash (s1:state_hash) (s2:state_hash) =
            s1.bad = true \/ s2.bad = true \/ Ok s1.l s2.l

assume val s : ref state_hash

assume val sample_hon : k0:key -> k1:key ->
                 ST2 (tag * tag)
                   (requires (fun _ -> True))
                   (ensures (fun h2' p h2 -> h2' = h2 /\ safe k0 k1 (fst p) (snd p)))
assume val sample_adv : unit ->
                 ST2 (tag * tag)
                   (requires (fun _ -> True))
                   (ensures (fun h2' p h2 -> h2' = h2 /\ fst p = snd p))

(* Actual non-relational code of hash_hon : *)
(*
let hash_hon k = match assoc k (!s),l with
  | Some (Hon,t) -> Some t
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = samle_hon k in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t
*)


val hash_hon:  k0:key -> k1:key ->
               ST2 (option tag * option tag)
               (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                          safe_key k0 k1))
               (ensures (fun _ p h2 -> (sel (fst h2) s).bad \/
                                       (sel (snd h2) s).bad \/
                                       (is_Some (fst p) /\ is_Some (snd p) /\
                                          safe k0 k1 (Some.v(fst p)) (Some.v(snd p))
                                          /\ Ok (sel (fst h2) s).l (sel (snd h2) s).l)))

val hash_hon2: k0:key -> k1:key ->
               ST2 (option tag * option tag)
               (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                          safe_key k0 k1))
               (ensures (fun _ p h2 -> (sel (fst h2) s).bad \/
                                       (sel (snd h2) s).bad \/
                                       (is_Some (fst p) /\ is_Some (snd p) /\
                                          safe k0 k1 (Some.v(fst p)) (Some.v(snd p))
                                          /\ Ok (sel (fst h2) s).l (sel (snd h2) s).l)))

val hash_adv:  k:key ->
               ST2 (option tag * option tag)
               (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s)))
               (ensures (fun _ p h2 -> (sel (fst h2) s).bad \/
                                       (sel (snd h2) s).bad \/
                                       is_Some (fst p) /\ is_Some (snd p) /\
                                          Some.v(fst p) = Some.v(snd p)
                                          /\ Ok (sel (fst h2) s).l (sel (snd h2) s).l))

(* workaround for some typing problems... *)
val add_some : tag -> Tot (option tag)
let add_some t = Some t

(* reordered version of the original program: We do not sample, but we get the
   sampled value as an argument. *)
let hash_hon' k r = match assoc k (!s).l with
  | Some (Hon,t) -> Some t
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t

let hash_hon k0 k1  = let r0, r1 = sample_hon k0 k1 in
                      (compose2 (fun k -> hash_hon' k r0)
                                (fun k -> hash_hon' k r1)
                                k0 k1)

let case_Hon  t     = Some t
let case_Adv  _     = s:={bad = true; l=(!s).l}; None
let case_None (k,t) = s:={bad = (!s).bad; l = (k,(Hon,t))::(!s).l}; add_some t

assume val sample_single : unit -> Tot tag

let hash_hon2 k0 k1 =
  let l0, l1 = compose2 (fun _ -> (!s).l) (fun _ -> (!s).l) () () in
  match assoc k0 l0, assoc k1 l1 with
  | Some (Hon,t0), Some (Hon,t1) -> compose2 (fun x -> case_Hon x) (fun x -> case_Hon x) t0 t1
  | Some (Hon,t0), Some (Adv,t1) -> compose2 (fun x -> case_Hon x) (fun x -> case_Adv x) t0 ()
  | Some (Hon,t0), None          -> let t1 = sample_single () in
                                    compose2 (fun x -> case_Hon x) (fun x -> case_None x) t0 (k1,t1)
  | Some (Adv,t0), Some (Hon,t1) -> compose2 (fun x -> case_Adv x) (fun x -> case_Hon x) () t0
  | Some (Adv,t0), Some (Adv,t1) -> compose2 (fun x -> case_Adv x) (fun x -> case_Adv x) () ()
  | Some (Adv,t0), None          -> let t1 = sample_single () in
                                    compose2 (fun x -> case_Adv x) (fun x -> case_None x) () (k1,t1)
  | None         , Some (Hon,t1) -> let t0 = sample_single () in
                                    compose2 (fun x -> case_None x) (fun x -> case_Hon x) (k0,t0) t1
  | None         , Some (Adv,t1) -> let t0 = sample_single () in
                                    compose2 (fun x -> case_None x) (fun x -> case_Adv x) (k0,t0) ()
  | None         , None          -> let t0, t1 = sample_hon k0 k1 in
                                    compose2 (fun x -> case_None x) (fun x -> case_None x) (k0,t0) (k1,t1)

let hash_adv' k r =  match assoc k (!s).l with
  | Some (Adv,t) -> Some t
  | Some (Hon,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Adv,t))::(!s).l} ;
                    add_some t


let hash_adv k  = let r0, r1 = sample_adv () in
                  compose2 (fun k -> hash_adv' k r0)
                           (fun k -> hash_adv' k r1)
                           k k

(* Simple Encryption Scheme based on ro *)

type injection (#a:Type) (f:a -> Tot a) = (forall x y. f x = f y ==> x = y)
type surjection (#a:Type) (f:a -> Tot a) = (forall y. (exists x. f x = y))
type bijection (#a:Type) (f:a -> Tot a) = injection f /\ surjection f

assume val sample : #a:Type
                    -> f:(a -> Tot a){bijection f}
                    -> ST2 (a * a)
                       (requires (fun _ -> True))
                       (ensures (fun h2' p  h2 -> h2' = h2 /\ fst p = f (snd p)))

assume val append : bytes -> bytes -> Tot bytes

type block = b:bytes{length(b)=eta}

assume val xor : block -> block -> Tot block

let xor_sym = assume(forall a b. xor a b = xor b a)
let xor_inv = assume(forall a b. xor (xor a b) a = b)
let xor_ass = assume(forall a b c. xor (xor a b) c = xor a (xor b c))
val xor_inj : a:block -> b:block -> c:block
              -> Lemma
              (requires (xor a b = xor a c))
              (ensures (b = c))
              [SMTPat (xor a b = xor a c)]
let xor_inj a b c = cut (b2t (xor (xor a b) a = xor (xor a c) a))

val encrypt : block -> block -> Tot block
let encrypt p k = xor p k
val decrypt : block -> block -> Tot block
let decrypt c k = xor c k

type state_enc =
  { bad': bool; (* set iff a nonce was sampled twice *)
    l':log }    (* the log keeps track of returned nonces *)

type good_state_enc (s:state_enc) = s.bad' = false
(*

val encrypt_hon : k0:bytes ->  k1:bytes -> p0:block -> p1:block ->
              ST2 (option(block * block) * option(block * block))
                  (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s)))
                  (ensures  (fun h2' p h2 -> (sel (fst h2) s).bad  \/
                                             (sel (snd h2) s).bad  \/
                                             Ok (sel (fst h2) s).l (sel (snd h2) s).l /\
                                             is_Some (fst p) /\ is_Some (snd p) /\
                                             fst p = snd p))
*)

(*
let encrypt_hon k0 k1 p0 p1 = let r0, r1 = sample (fun x ->  x) in
                  let h0, h1 = hash_hon (append k0 r0) (append k1 r1) in
                  compose2 (fun (p,h,r) -> if is_Some h then Some ((encrypt p (Some.v h)),r) else None)
                           (fun (p,h,r) -> if is_Some h then Some ((encrypt p (Some.v h)),r) else None)
                           (p0, h0, r0) (p1, h1, r1)
*)
