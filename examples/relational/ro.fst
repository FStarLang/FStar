(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 15  --print_implicits;
    other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Relational.fst FStar.Bytes.fst FStar.List.fst sample.fst xor.fst
  --*)

module Ro

open FStar.Comp
open FStar.Heap
open FStar.List
open FStar.Bytes
open Xor
open Bijection
open Sample
open FStar.Relational

type map (a:Type) (b:Type) = list (a * b)

type key = bytes
type tag = block

(* Two keys are safe to be used for sampling, if they are related by some
   bijection *)
assume val safe_key_rel_fun :f:(key -> Tot key){good_sample_fun #key #key f}
let safe_key (k:double key) = R.r k = safe_key_rel_fun (R.l k)

val safe_key_unique : k0:key -> k0':key -> k1:key ->
  Lemma (requires (safe_key (R k0 k1) /\ safe_key (R k0' k1)))
        (ensures (k0 = k0'))
let safe_key_unique k0 k0' k1 =
  good_sample_fun_bijection safe_key_rel_fun

(* correctly-generated are always related by some bijection *)
opaque type safe (t:double tag) = (exists (f:bij #tag #tag). R.r t = f (R.l t))


(* a "ghost" field recording the first allocator for a given key *)
type alloc =
  | Hon: alloc
  | Adv: alloc 

type log = map key (alloc * tag)

type state_hash =
  { bad: bool; (* set iff any allocation has failed, 
                  e.g. bumped into the other's table *)
    l:log }    (* the map ensures at most one entry per key *)


(* relational invariant for correct logs *)
type Ok : double log -> Type =
  | Null: Ok (twice [])
  | ConsH: k:double key{safe_key k} -> t:double tag{safe t}
           -> l:double log{and_irel (rel_map2T (fun k l -> is_None (assoc k l)) k l)}
           -> p: Ok l
           -> Ok (cons_rel (pair_rel k (pair_rel (twice Hon) t)) l)
  | ConsA: k:eq key -> t:eq tag
           -> l:double log{and_irel (rel_map2T (fun k l -> is_None (assoc k l)) k l)}
           -> p: Ok l
           -> Ok (cons_rel (pair_rel k (pair_rel (twice Adv) t)) l)

(* keys are fresh if they are not in the hash function's log yet *)
val fresh_keys : k:double key -> l:double log -> Tot bool
let fresh_keys k l = and_irel (rel_map2T (fun k l -> is_None (assoc k l)) k l)

(* We need these lemmas to use our inductive datatype Ok without having access
   to an element of Ok l (it exists only in refinements) *)
assume val ok_as_refinement : #l:double log  -> p:Ok l -> Tot (u:unit{Ok l})
assume val ok_as_proof : l: double log{Ok l} -> Tot (Ok l)

val ok_consH : k:double key{safe_key k}
             -> t:double tag{safe t}
             -> l:double log{and_irel (rel_map2T (fun k l  -> is_None (assoc k l)) k l)
                          /\ Ok l}
             ->  Lemma (requires True)
                       (ensures Ok (cons_rel (pair_rel k (pair_rel (twice Hon) t)) l))
let ok_consH k t l = ok_as_refinement(ConsH k t l (ok_as_proof l))

val ok_consA : k:eq key
             -> t:eq tag
             -> l:double log{and_irel (rel_map2T (fun k l  -> is_None (assoc k l)) k l)
                          /\ Ok l}
             ->  Lemma (requires True)
                       (ensures Ok (cons_rel (pair_rel k (pair_rel (twice Adv) t)) l))
let ok_consA k t l = ok_as_refinement(ConsA k t l (ok_as_proof l))

(* Adversary lookups on both sides always return equal results for Ok logs *)
val ok_adv_eq' : k:eq key -> l:double log -> p:Ok l
                -> Lemma
                   (requires True)
                   (ensures (forall t. assoc (R.l k) (R.l l) = Some(Adv, t) <==>
                                       assoc (R.r k) (R.r l) = Some(Adv, t)))
                   (decreases (R.l l))
let rec ok_adv_eq' k l p = match p with
        | Null -> ()
        | ConsH _ _ tl p' -> ok_adv_eq' k tl p'
        | ConsA _ _ tl p' -> ok_adv_eq' k tl p'


val ok_adv_eq : k:eq key -> l:double log{Ok l}
                -> Lemma
                   (requires True)
                   (ensures (forall t. assoc (R.l k) (R.l l) = Some(Adv, t) <==>
                                       assoc (R.r k) (R.r l) = Some(Adv, t)))
let ok_adv_eq k l = ok_adv_eq' k l (ok_as_proof l)


(* Honest lookups either hit in both or no logs for Ok logs and safe keys *)
val ok_hon_safe' : k:double key -> l:double log -> p:Ok l
                -> Lemma
                   (requires (safe_key k))
                   (ensures ( (is_Some(assoc (R.l k) (R.l l)) /\ is_Hon(fst (Some.v(assoc (R.l k) (R.l l))))) <==>
                               is_Some(assoc (R.r k) (R.r l)) /\ is_Hon(fst (Some.v(assoc (R.r k) (R.r l))))))
                   (decreases (R.l l))
let rec ok_hon_safe' k l p = match p with
        | Null -> ()
        | ConsH k' t' tl p' -> ok_hon_safe' k tl p';
                               if safe_key (R (R.l k) (R.r k)) && safe_key (R (R.l k') (R.r k)) then
                                 safe_key_unique (R.l k) (R.l k') (R.r k);
                               if safe_key (R (R.l k) (R.r k')) && safe_key (R (R.l k') (R.r k')) then
                                 safe_key_unique (R.l k) (R.l k') (R.r k')
        | ConsA k' t' tl p' -> ok_hon_safe' k tl p'

 val ok_hon_safe : k:double key -> l:double log{Ok l}
                -> Lemma
                   (requires (safe_key k))
                   (ensures ( (is_Some(assoc (R.l k) (R.l l)) /\ is_Hon(fst (Some.v(assoc (R.l k) (R.l l))))) <==>
                               is_Some(assoc (R.r k) (R.r l)) /\ is_Hon(fst (Some.v(assoc (R.r k) (R.r l))))))
let ok_hon_safe k l = ok_hon_safe' k l (ok_as_proof l)


(* Honest lookups return safe tags if both lookups hit (for safe keys and Ok
   logs) *)
val ok_hon_safe2' : k:double key -> l:double log -> p:Ok l
                -> Lemma
                   (requires (safe_key k))
                   (ensures (is_Some(assoc (R.l k) (R.l l)) /\ is_Some(assoc (R.r k) (R.r l)) /\
                             is_Hon(fst(Some.v (assoc (R.l k) (R.l l)))) /\
                             is_Hon(fst(Some.v (assoc (R.r k) (R.r l)))) ==>
                               safe (R (snd(Some.v (assoc (R.l k) (R.l l))))
                                       (snd(Some.v (assoc (R.r k) (R.r l)))))))
                   (decreases (R.l l))
let rec ok_hon_safe2' k l p = match p with
        | Null -> ()
        | ConsH k' t tl p' -> ok_hon_safe2' k tl p';
                             if safe_key (R (R.l k) (R.r k)) && safe_key (R (R.l k') (R.r k)) then
                               safe_key_unique (R.l k) (R.l k') (R.r k);
                             if safe_key (R (R.l k) (R.r k')) && safe_key (R (R.l k') (R.r k')) then
                               safe_key_unique (R.l k) (R.l k') (R.r k')
        | ConsA _ t tl p' -> ok_hon_safe2' k tl p'

val ok_hon_safe2 : k:double key -> l:double log{Ok l}
                -> Lemma
                   (requires (safe_key k))
                   (ensures (is_Some(assoc (R.l k) (R.l l)) /\ is_Some(assoc (R.r k) (R.r l)) /\
                             is_Hon(fst(Some.v (assoc (R.l k) (R.l l)))) /\
                             is_Hon(fst(Some.v (assoc (R.r k) (R.r l)))) ==>
                               safe (R (snd(Some.v (assoc (R.l k) (R.l l))))
                                       (snd(Some.v (assoc (R.r k) (R.r l)))))))
let ok_hon_safe2 k l = ok_hon_safe2' k l (ok_as_proof l)

(* Invariant on our state: either we have a bad event in one of the two runs or
   our logs are Ok *)
type goodstate_hash (s:double state_hash) =
            (R.l s).bad \/ (R.r s).bad
            \/ ~((R.l s).bad \/ (R.r s).bad) /\ Ok (rel_map1T (fun s -> s.l) s)

assume val s :  (ref state_hash)

(* We prove the same signature for honest hashing in two different ways *)
opaque val hash_hon:  k:double key -> f:(tag -> Tot tag){good_sample_fun #tag #tag f} ->
               ST2 (double (option tag))
               (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s) /\
                          safe_key k))
               (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s) /\
                                         (not (or_irel (rel_map1T (fun s -> s.bad) (sel_rel1 h2 s))) ==>
                                         (is_Some (R.l p) /\ is_Some (R.r p)
                                           /\ safe (R (Some.v(R.l p)) (Some.v(R.r p)))
                                           /\ (fresh_keys k (rel_map1T (fun s -> s.l) (sel_rel1 h2' s))
                                               ==> Some.v #tag (R.r p) = f (Some.v #tag (R.l p)))
                                           /\ Ok (rel_map1T (fun s -> s.l)(sel_rel1 h2 s))))))

opaque val hash_hon2:  k:double key -> f:(tag -> Tot tag){good_sample_fun #tag #tag f} ->
               ST2 (double (option tag))
               (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s) /\
                          safe_key k))
               (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s) /\
                                         (not (or_irel (rel_map1T (fun s -> s.bad) (sel_rel1 h2 s))) ==>
                                         (is_Some (R.l p) /\ is_Some (R.r p)
                                           /\ safe (R (Some.v(R.l p)) (Some.v(R.r p)))
                                           /\ (fresh_keys k (rel_map1T (fun s -> s.l) (sel_rel1 h2' s))
                                               ==> Some.v #tag (R.r p) = f (Some.v #tag (R.l p)))
                                           /\ Ok (rel_map1T (fun s -> s.l)(sel_rel1 h2 s))))))

opaque val hash_adv: k:eq key ->
               ST2 (double (option tag))
               (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s)))
               (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s) /\
                                         (or_irel (rel_map1T (fun s -> s.bad) (sel_rel1 h2 s)) \/
                                         is_Some (R.l p) /\ is_Some (R.r p) /\
                                         Some.v(R.l p) = Some.v(R.r p)
                                         /\ Ok (rel_map1T (fun s -> s.l)(sel_rel1 h2 s)))))

(* workaround for some typing problems *)
val add_some : tag -> Tot (option tag)
let add_some t = Some t

(* Actual non-relational code of hash_hon : *)
(*
let hash_hon k = match assoc k (!s),l with
  | Some (Hon,t) -> Some t
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = sample k in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t
*)


(* reordered version of the original program: We do not sample, but we get the
   sampled value as an argument. *)
let hash_hon' k r = match assoc k (!s).l with
  | Some (Hon,t) -> Some t
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t

(* We use this reordered version to do the actual proof only by compose2 *)
let hash_hon k f = let s = compose2_self (fun s -> !s) (twice s)in
                   let l = rel_map1T (fun s -> s.l) s in

                   (* Actual code. The rest is just to apply the correct lemmas *)
                   let r = sample #tag #tag f in
                   let t = compose2_self (fun (k,r) -> hash_hon' k r)
                                         (pair_rel k r) in

                   good_sample_fun_bijection #tag #tag f;
                   if (not (or_irel (rel_map1T (fun s -> s.bad) s))) then
                     if and_irel (rel_map1T is_Some t) then
                       (ok_hon_safe k l;
                       ok_hon_safe2 k l;
                       if and_irel (rel_map2T (fun k l -> is_None (assoc k l)) k l) then
                         ok_consH k (R (Some.v (R.l t)) (Some.v (R.r t))) l);
                   t

(* The three code pieces that occur in the three match cases of the single
   sided variant *)
let case_Hon  t     = Some t
let case_Adv  ()    = s:={bad = true; l=(!s).l}; None #tag
let case_None (k,t) = s:={bad = (!s).bad; l = (k,(Hon,t))::(!s).l}; add_some t

(* To deal with cross cases where we only sample on one side, we need a
   single-sided sample *)
assume val sample_single : unit -> Tot tag

(* We do a manual interleaving (This is necessary if we don't want to move
   sample as shown above). *)
let hash_hon2 k f =
  let s = compose2_self (fun s -> !s) (twice s) in
  let l = rel_map1T (fun s -> s.l) s in
  let b = or_irel (rel_map1T (fun s -> s.bad) s) in
  match rel_map2T assoc k l with
  | R (Some (Hon,t0)) (Some (Hon,t1)) -> if not b then
                                           ok_hon_safe2 k l;
                                         compose2_self (fun x -> case_Hon x) (R t0 t1)
  | R (Some (Hon,t0)) (Some (Adv,t1)) -> compose2 (fun x -> case_Hon x) (fun x -> case_Adv x) (R t0 ())
  | R (Some (Hon,t0)) (None         ) -> if not b then
                                           ok_hon_safe k l;
                                         compose2 (fun (_ ,x) -> case_Hon x) 
                                                  (fun x -> case_None x) 
                                                  (pair_rel k (R t0 (sample_single ())))
  | R (Some (Adv,t0)) (Some (Hon,t1)) -> compose2 (fun x -> case_Adv x) (fun x -> case_Hon x) (R () t1)
  | R (Some (Adv,t0)) (Some (Adv,t1)) -> compose2_self (fun x -> case_Adv x) (twice ())
  | R (Some (Adv,t0)) (None         ) -> compose2 (fun (_, x) -> case_Adv x) 
                                                  (fun x -> case_None x) 
                                                  (pair_rel k (R () (sample_single ())))
  | R (None         ) (Some (Hon,t1)) -> if not b then
                                           ok_hon_safe k l;
                                         compose2 (fun x -> case_None x) 
                                                  (fun (_, x) -> case_Hon x) 
                                                  (pair_rel k (R (sample_single ()) t1))
  | R (None         ) (Some (Adv,t1)) -> compose2 (fun x -> case_None x) 
                                                  (fun (k, x) -> case_Adv x)
                                                  (pair_rel k (R (sample_single ()) () ))
  | R (None         ) (None         ) -> let t = sample #tag #tag f in
                                         good_sample_fun_bijection #tag #tag f;
                                         if not b then
                                           ok_consH k t l;
                                         compose2_self (fun x -> case_None x) (pair_rel k t) 

(* For adversarial hashes we again move sample to the beginning of the function *)
let hash_adv' k r =  match assoc k (!s).l with
  | Some (Adv,t) -> Some t
  | Some (Hon,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Adv,t))::(!s).l} ;
                    add_some t

let hash_adv k  = let s = compose2_self (fun s -> !s) (twice s) in
                  let l = rel_map1T (fun s -> s.l) s in

                  (* Actual code, the rest is just for calling lemmas *)
                  cut(bijection #tag #tag  (fun x -> x));
                  bijection_good_sample_fun #tag #tag (fun x -> x);
                  let r = sample (fun x->x) in
                  let t = compose2_self (fun (k,r) -> hash_adv' k r)
                                        (pair_rel k r) in 

                  if (not (or_irel (rel_map1T (fun s -> s.bad) s))) then
                    if and_irel (rel_map1T is_Some t) then
                      (ok_adv_eq k l;
                      if and_irel (rel_map2T (fun k l -> is_None (assoc k l)) k l) then
                        ok_consA k (R (Some.v (R.l t)) (Some.v (R.r t))) l);
                  t

(* Simple Encryption Scheme based on ro *)
module Encryption

open FStar.Comp
open FStar.Heap
open Bijection
open Sample
open FStar.Relational
open Xor
open FStar.Bytes
open FStar.List
open Ro

assume val append : bytes -> bytes -> Tot bytes

(* We use a simple OTP as basis block for our encryption scheme *)
val encrypt : block -> block -> Tot block
let encrypt p k = xor p k
val decrypt : block -> block -> Tot block
let decrypt c k = xor c k

(* As our hash-key will be created by appending a random string to our
   encryption key, we need to require that encryption keys are prefixes of safe
   hash keys *)
opaque type safe_key_pre (k:double bytes) = 
  (forall (r:block). safe_key (rel_map2T append k (twice r)))

(* We prove that our sampling function is a bijection *)
opaque val encrypt_good_sample_fun : p1:block -> p2:block
  -> Lemma (good_sample_fun #block #block (fun x -> xor (xor p1 p2) x))
let encrypt_good_sample_fun p1 p2 =
  let sample_fun = (fun x -> xor (xor p1 p2) x) in
  cut (bijection #block #block sample_fun);
  bijection_good_sample_fun #block #block sample_fun

(* We prove that the identity function used for sampling  is a bijection *)
opaque val id_good_sample_fun : unit -> Lemma (good_sample_fun #block #block (fun x -> x))
let id_good_sample_fun () =
  cut (bijection #block #block (fun x -> x));
  bijection_good_sample_fun #block #block (fun x -> x)

#reset-options
(* If the random oracle is not in a bad state and if we used fresh hash-keys,
   then we can show that two the ciphertexts are equal *)
opaque val encrypt_hon : k:double key{safe_key_pre k}
                  -> p:double block ->
                  ST2 (double (option (block * block)))
                 (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s)))
                 (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s)
                                           /\( not (or_irel (rel_map1T (fun s -> s.bad) (sel_rel1 h2 s)))
                                             ==> Ok (rel_map1T (fun s -> s.l)(sel_rel1 h2 s))
                                             /\ is_Some (R.l p) /\ is_Some (R.r p)
                                             /\ snd (Some.v (R.l p)) = snd (Some.v (R.r p))
                                             /\ (fresh_keys (rel_map2T append k (R (snd(Some.v #(block * block) (R.l p)))
                                                                                  (snd(Some.v #(block * block) (R.r p)))))
                                                            (rel_map1T (fun s -> s.l) (sel_rel1 h2' s))
                                                            ==> eq_irel p))))
#reset-options
let encrypt_hon k p =
                  let sample_fun = (fun x -> xor (xor (R.l p) (R.r p)) x) in
                  id_good_sample_fun ();
                  encrypt_good_sample_fun (R.l p) (R.r p);
                  let r = sample #block #block (fun x -> x) in
                  let kh = rel_map2T append k r in

                  let h = hash_hon kh sample_fun in
                  (* Writing the code in this style causes the loss of some typing information *)
(*                   let c = rel_map3 (fun h p r -> if is_Some h then Some ((encrypt p (Some.v h)), r) else None) h p r in *)
                  let c = R (if is_Some (R.l h) then Some ((encrypt (R.l p) (Some.v (R.l h))), (R.l r)) else None)
                            (if is_Some (R.r h) then Some ((encrypt (R.r p) (Some.v (R.r h))), (R.r r)) else None) in 
                  c

(* We only show that decryption does not violate our relational invariants *)
#reset-options
opaque val decrypt_hon : k:double bytes{safe_key_pre k} ->
                  c:double(block * block){snd (R.l c) = snd (R.r c)} ->
                  ST2 (double (option block))
                 (requires (fun h2 -> goodstate_hash (sel_rel1 h2 s)))
                 (ensures (fun h2' p h2 -> goodstate_hash (sel_rel1 h2 s)))
let decrypt_hon k c =
                  let r = snd_rel c in
                  let kh = rel_map2T append k r in
                  id_good_sample_fun ();
                  let h = hash_hon kh (fun x -> x) in
                  (* Writing the code in this style causes the loss of some typing information *)
(*                   rel_map2T (fun h c -> if is_Some h then Some (decrypt (fst c) (Some.v h)) else None) h c *)
                  R (if is_Some (R.l h) then Some (decrypt (fst (R.l c)) (Some.v (R.l h))) else None)
                    (if is_Some (R.r h) then Some (decrypt (fst (R.r c)) (Some.v (R.r h))) else None)
