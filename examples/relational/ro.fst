(*--build-config
    options:--admit_fsi Set --z3timeout 30;
    variables:LIB=../../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/st2.fst $LIB/bytes.fst $LIB/list.fst sample.fst xor.fst
  --*)

module Ro

open Comp
open Heap
open List
open Bytes
open Xor
open Bijection
open Sample

type map (a:Type) (b:Type) = list (a * b)

type key = bytes
type tag = block

(* an abstract relational predicate on correctly-generated entries *)
opaque type safe_key (k0:key) (k1:key) = (exists (f:bij #key #key). k1 = f k0)
(*  type safe_key (k0:key) (k1:key) = k0 = k1 *)
assume Safe_key_unique  : (forall k0 k1 k1'.
                               {:pattern (safe_key k0 k1); (safe_key k0 k1')}
                               (safe_key k0 k1 /\ safe_key k0 k1' ==> k1 = k1'))
assume Safe_key_unique  : (forall k0 k0' k1.
                               {:pattern (safe_key k0 k1); (safe_key k0' k1)}
                               (safe_key k0 k1 /\ safe_key k0' k1 ==> k0 = k0'))
opaque type safe (t0:tag) (t1:tag) = (exists (f:bij #tag #tag). t1 = f t0)

 val bij2safe : f:bij #tag #tag -> t0:tag -> t1:tag ->
               Lemma (requires (t1 = f t0))
                     (ensures  (safe t0 t1))
let bij2safe f t0 t1 = ()

type alloc =
  | Hon: alloc
  | Adv: alloc (* a "ghost" field recording the first allocator for a given key *)

type log = map key (alloc * tag)

type state_hash =
  { bad: bool; (* set iff any allocation has failed, e.g. bumped into the other's table *)
    l:log }    (* the map ensures at most one entry per key *)


type Ok : log -> log -> Type =
  | Null: Ok [] []
  | ConsH: k0:key -> k1:key{safe_key k0 k1} -> t0:tag -> t1:tag{safe t0 t1}
           -> log0:log{is_None (assoc k0 log0)}
           -> log1:log{is_None (assoc k1 log1)}
           -> p: Ok log0 log1
           -> Ok ((k0,(Hon,t0))::log0) ((k1,(Hon,t1))::log1)
  | ConsA: k:key -> t:tag
           -> log0:log{is_None (assoc k log0)}
           -> log1:log{is_None (assoc k log1)}
           -> p: Ok log0 log1
           -> Ok ((k ,(Adv,t ))::log0) ((k, (Adv,t ))::log1)

val fresh_keys : k0:key -> k1:key -> l0:log -> l1:log -> Tot bool
let fresh_keys k0 k1 l0 l1 = is_None (assoc k0 l0) && is_None (assoc k1 l1)

assume val ok_as_refinement : #l0:log -> #l1:log  -> p:Ok l0 l1 -> Tot (u:unit{Ok l0 l1})
assume val ok_as_proof : l0:log -> l1:log{Ok l0 l1} -> Tot (Ok l0 l1)

 val ok_consH : k0:key -> k1:key{safe_key k0 k1} -> t0:tag
              -> t1:tag{safe t0 t1}
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
                               safe (snd(Some.v (assoc k0 l0))) (snd(Some.v (assoc k1 l1)))))
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
                                safe (snd(Some.v (assoc k0 l0))) (snd(Some.v (assoc k1 l1)))))
                                [SMTPat (assoc k0 l0); SMTPat (assoc k1 l1)]
let ok_hon_safe2 k0 k1 l0 l1 = ok_hon_safe2' k0 k1 l0 l1 (ok_as_proof l0 l1)
type goodstate_hash (s1:state_hash) (s2:state_hash) =
            s1.bad = true \/ s2.bad = true \/ Ok s1.l s2.l

assume val s : ref state_hash

(* Actual non-relational code of hash_hon : *)
(*
let hash_hon k = match assoc k (!s),l with
  | Some (Hon,t) -> Some t
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = samle_hon k in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t
*)


opaque val hash_hon:  k0:key -> k1:key -> f:bij #tag #tag ->
               ST2 (option tag * option tag)
               (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                          safe_key k0 k1))
               (ensures (fun h2' p h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                                       ((sel (fst h2) s).bad  \/
                                       (sel (snd h2) s).bad \/
                                       (is_Some (fst p) /\ is_Some (snd p) /\
                                          safe (Some.v(fst p)) (Some.v(snd p))
                                          /\ (fresh_keys k0 k1 ((sel (fst h2') s).l) ((sel (snd h2') s).l)
                                              ==> Some.v (snd p) = f (Some.v (fst p)))
                                          /\ Ok (sel (fst h2) s).l (sel (snd h2) s).l))))

                                  (* Why does (f:bij #tag #tag) not work here?*)
opaque val hash_hon2: k0:key -> k1:key -> f:(tag -> Tot tag){bijection f} ->
               ST2 (option tag * option tag)
               (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                          safe_key k0 k1))
               (ensures (fun h2' p h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                                       ((sel (fst h2) s).bad  \/
                                       (sel (snd h2) s).bad \/
                                       (is_Some (fst p) /\ is_Some (snd p) /\
                                          safe (Some.v(fst p)) (Some.v(snd p))
                                          /\ (fresh_keys k0 k1 ((sel (fst h2') s).l) ((sel (snd h2') s).l)
                                              ==> Some.v (snd p) = f (Some.v (fst p)))
                                          /\ Ok (sel (fst h2) s).l (sel (snd h2) s).l))))
opaque val hash_adv:  k:key ->
               ST2 (option tag * option tag)
               (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s)))
               (ensures (fun h2' p h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                                       ((sel (fst h2) s).bad  \/
                                       (sel (snd h2) s).bad \/
                                       is_Some (fst p) /\ is_Some (snd p) /\
                                          Some.v(fst p) = Some.v(snd p)
                                          /\ Ok (sel (fst h2) s).l (sel (snd h2) s).l)))

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

let hash_hon k0 k1 f = let r0, r1 = sample f in
                      (compose2 (fun k -> hash_hon' k r0)
                                (fun k -> hash_hon' k r1)
                                k0 k1)

let case_Hon  t     = Some t
let case_Adv  _     = s:={bad = true; l=(!s).l}; None
let case_None (k,t) = s:={bad = (!s).bad; l = (k,(Hon,t))::(!s).l}; add_some t

assume val sample_single : unit -> Tot tag

let hash_hon2 k0 k1 f =
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
  | None         , None          -> let t0, t1 = sample f in
                                    compose2 (fun x -> case_None x) (fun x -> case_None x) (k0,t0) (k1,t1)

let hash_adv' k r =  match assoc k (!s).l with
  | Some (Adv,t) -> Some t
  | Some (Hon,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Adv,t))::(!s).l} ;
                    add_some t


let hash_adv k  = let r0, r1 = sample (fun x->x) in
                  compose2 (fun k -> hash_adv' k r0)
                           (fun k -> hash_adv' k r1)
                           k k


(* Simple Encryption Scheme based on ro *)
module Encryption

open Comp
open Heap
open Bijection
open Sample
open Xor
open Bytes
open List
open Ro


assume val append : bytes -> bytes -> Tot bytes

val encrypt : block -> block -> Tot block
let encrypt p k = xor p k
val decrypt : block -> block -> Tot block
let decrypt c k = xor c k

opaque type safe_key_pre (k0:bytes) (k1:bytes) = (forall (r:block). safe_key (append k0 r) (append k1 r))

val lemma_safe_key_pre : k0:bytes -> k1:bytes{safe_key_pre k0 k1} -> r0:block -> r1:block{r0=r1}
                         -> Lemma (safe_key (append k0 r0) (append k1 r1))
let lemma_safe_key_pre k0 k1 r0 r1 = ()

(* using this pair at a fixed type because of problems probably related to #290 *)
type mp : Type =
  | MkMP : a:block -> b:block -> mp



opaque val xor_inverse_lemma : a:block -> Lemma (bijection #block #block (fun x -> xor a x))
let xor_inverse_lemma a = ()

opaque val encrypt_equal_lemma: x:block -> y:block ->  p0:block -> p1:block -> Lemma (y = xor (xor p0 p1) x ==> encrypt p0 x = encrypt p1 y)
let encrypt_equal_lemma x y p0 p1 = ()


val encrypt_hon : k0:bytes ->  k1:bytes{safe_key_pre k0 k1}
                  -> p0:block-> p1:block ->
                  ST2 (option mp * option mp)
                  (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s)))
                  (ensures  (fun h2' p h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s) /\
                                             (~((sel (fst h2) s).bad  \/
                                             (sel (snd h2) s).bad)  ==>
                                             Ok (sel (fst h2) s).l (sel (snd h2) s).l /\
                                             is_Some (fst p) /\ is_Some (snd p)   /\
                                             (fresh_keys (append k0 (MkMP.b(Some.v (fst p))))
                                                         (append k1 (MkMP.b(Some.v (snd p))))
                                                         ((sel (fst h2') s).l)
                                                         ((sel (snd h2') s).l) ==>
                                                  fst p = snd p))))
let encrypt_hon k0 k1 p0 p1 =
                  let sample_fun = (fun x -> xor (xor p0 p1) x) in
                  xor_inverse_lemma (xor p0 p1);
                  cut(bijection #block #block sample_fun);
                  let r0, r1 = sample (fun x ->  x) in
                  let kh0, kh1 = append k0 r0, append k1 r1 in
                  lemma_safe_key_pre k0 k1 r0 r1;
                  cut (safe_key kh0 kh1);
                  let l0, l1 = compose2 (fun () -> (!s).l) (fun () -> (!s).l) () () in
                  let h0, h1 = hash_hon kh0 kh1 (sample_fun)  in
                  let s0, s1 = compose2 (fun () -> (!s)) (fun () -> (!s)) () () in
                  let a = if is_Some h0 then Some (MkMP (encrypt p0 (Some.v h0)) r0) else None in
                  let b = if is_Some h1 then Some (MkMP (encrypt p1 (Some.v h1)) r1) else None in
                  if not (s0.bad || s1.bad) then
                    if (fresh_keys kh0 kh1 l0 l1) then(
                      cut (b2t(Some.v h1 = sample_fun (Some.v h0)));
                      encrypt_equal_lemma (Some.v h0) (Some.v h1) p0 p1;
                      cut (b2t(encrypt p0 (Some.v h0) = encrypt p1 (Some.v h1)));
                      cut (b2t(a = b))
                      );
                  a,b

(*
val decrypt_hon : k0:bytes -> k1:bytes{safe_key_pre k0 k1} ->
                  c0:mp -> c1:mp{c0 = c1} ->
                  ST2 (option block * option block)
                  (requires (fun h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s)))
                  (ensures  (fun h2' p h2 -> goodstate_hash (sel (fst h2) s) (sel (snd h2) s)))
let decrypt_hon k0 k1 (MkMP c0 r0) (MkMP c1 r1) = 
                  let kh0, kh1 = append k0 r0, append k1 r1 in
                  let h0, h1 = hash_hon kh0 kh1 (fun x -> x) in
                  let a = if is_Some h0 then Some (decrypt c0 (Some.v h0)) else None in
                  let b = if is_Some h1 then Some (decrypt c0 (Some.v h1)) else None in
                  a, b
*)
