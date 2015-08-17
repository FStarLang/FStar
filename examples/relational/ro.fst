(*--build-config
    options:--admit_fsi Set --z3timeout 5  --print_implicits;
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
open Relational

type map (a:Type) (b:Type) = list (a * b)

type key = bytes
type tag = block

(* an abstract relational predicate on correctly-generated entries *)
assume val safe_key_rel_fun :f:(key -> Tot key){good_sample_fun #key #key f}
let safe_key (k:double key) = R.r k= safe_key_rel_fun (R.l k)

val safe_key_unique : k0:key -> k0':key -> k1:key ->
  Lemma (requires (safe_key (R k0 k1) /\ safe_key (R k0' k1)))
        (ensures (k0 = k0'))
let safe_key_unique k0 k0' k1 =
  good_sample_fun_bijection safe_key_rel_fun;
  (* Injectivity should follow from bijectivity, howere types are opaque, so assuming *)
  assume (forall (x:key) (y:key). safe_key_rel_fun x = safe_key_rel_fun y ==> x = y)

(*
assume Safe_key_unique  : (forall k0 k0' k1.
                               {:pattern (safe_key (R k0 k1)); (safe_key (R k0' k1))}
                               (safe_key (R k0 k1) /\ safe_key (R k0' k1) ==> k0 = k0'))
*)

opaque type safe (t:double tag) = (exists (f:bij #tag #tag). R.r t = f (R.l t))

type alloc =
  | Hon: alloc
  | Adv: alloc (* a "ghost" field recording the first allocator for a given key *)

type log = map key (alloc * tag)

type state_hash =
  { bad: bool; (* set iff any allocation has failed, e.g. bumped into the other's table *)
    l:log }    (* the map ensures at most one entry per key *)


type Ok : double log -> Type =
  | Null: Ok (twice [])
  | ConsH: k:double key{safe_key k} -> t:double tag{safe t}
           -> l:double log{and_rel (rel_map2 (fun k l  -> is_None (assoc k l)) k l)}
           -> p: Ok l
           -> Ok (cons_rel (pair_rel k (pair_rel (twice Hon) t)) l)
  | ConsA: k:eq key -> t:eq tag
           -> l:double log{and_rel (rel_map2 (fun k l  -> is_None (assoc k l)) k l)}
           -> p: Ok l
           -> Ok (cons_rel (pair_rel k (pair_rel (twice Adv) t)) l)

val fresh_keys : k:double key -> l:double log -> Tot bool
let fresh_keys k l = and_rel (rel_map2 (fun k l -> is_None (assoc k l)) k l)

assume val ok_as_refinement : #l:double log  -> p:Ok l -> Tot (u:unit{Ok l})
assume val ok_as_proof : l: double log{Ok l} -> Tot (Ok l)

 val ok_consH : k:double key{safe_key k}
             -> t:double tag{safe t}
             -> l:double log{and_rel (rel_map2 (fun k l  -> is_None (assoc k l)) k l)
                          /\ Ok l}
             ->  Lemma (requires True)
                       (ensures Ok (cons_rel (pair_rel k (pair_rel (twice Hon) t)) l))
let ok_consH k t l = ok_as_refinement(ConsH k t l (ok_as_proof l))

 val ok_consA : k:eq key
             -> t:eq tag
             -> l:double log{and_rel (rel_map2 (fun k l  -> is_None (assoc k l)) k l)
                          /\ Ok l}
             ->  Lemma (requires True)
                       (ensures Ok (cons_rel (pair_rel k (pair_rel (twice Adv) t)) l))
let ok_consA k t l = ok_as_refinement(ConsA k t l (ok_as_proof l))

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

type goodstate_hash (s:double state_hash) =
            (R.l s).bad \/ (R.r s).bad
            \/ ~((R.l s).bad \/ (R.r s).bad) /\ Ok (rel_map1 (fun s -> s.l) s)

assume val s :  (ref state_hash)

(* Actual non-relational code of hash_hon : *)
(*
let hash_hon k = match assoc k (!s),l with
  | Some (Hon,t) -> Some t
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = samle_hon k in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t
*)


opaque val hash_hon:  k:double key -> f:(tag -> Tot tag){good_sample_fun #tag #tag f} ->
               ST2 (double (option tag))
               (requires (fun h2 -> goodstate_hash (sel_rel h2 (twice s)) /\
                          safe_key k))
               (ensures (fun h2' p h2 -> goodstate_hash (sel_rel h2 (twice s)) /\
                                         (not (or_rel (rel_map1 (fun s -> s.bad) (sel_rel h2 (twice s)))) ==>
                                         (is_Some (R.l p) /\ is_Some (R.r p)
                                           /\ safe (R (Some.v(R.l p)) (Some.v(R.r p)))
                                           /\ (fresh_keys k (rel_map1 (fun s -> s.l) (sel_rel h2' (twice s)))
                                               ==> Some.v #tag (R.r p) = f (Some.v #tag (R.l p)))
                                           /\ Ok (rel_map1 (fun s -> s.l)(sel_rel h2 (twice s)))))))

opaque val hash_hon2:  k:double key -> f:(tag -> Tot tag){good_sample_fun #tag #tag f} ->
               ST2 (double (option tag))
               (requires (fun h2 -> goodstate_hash (sel_rel h2 (twice s)) /\
                          safe_key k))
               (ensures (fun h2' p h2 -> goodstate_hash (sel_rel h2 (twice s)) /\
                                         (not (or_rel (rel_map1 (fun s -> s.bad) (sel_rel h2 (twice s)))) ==>
                                         (is_Some (R.l p) /\ is_Some (R.r p)
                                           /\ safe (R (Some.v(R.l p)) (Some.v(R.r p)))
                                           /\ (fresh_keys k (rel_map1 (fun s -> s.l) (sel_rel h2' (twice s)))
                                               ==> Some.v #tag (R.r p) = f (Some.v #tag (R.l p)))
                                           /\ Ok (rel_map1 (fun s -> s.l)(sel_rel h2 (twice s)))))))

opaque val hash_adv: k:eq key ->
               ST2 (double (option tag))
               (requires (fun h2 -> goodstate_hash (sel_rel h2 (twice s))))
               (ensures (fun h2' p h2 -> goodstate_hash (sel_rel h2 (twice s)) /\
                                         (or_rel (rel_map1 (fun s -> s.bad) (sel_rel h2 (twice s))) \/
                                         is_Some (R.l p) /\ is_Some (R.r p) /\
                                         Some.v(R.l p) = Some.v(R.r p)
                                         /\ Ok (rel_map1 (fun s -> s.l)(sel_rel h2 (twice s))))))

(* workaround for some typing problems... *)
val add_some : tag -> Tot (option tag)
let add_some t = Some t

(* reordered version of the original program: We do not sample, but we get the
   sampled value as an argument. *)
let hash_hon' k r = match assoc k (!s).l with
  | Some (Hon,t) -> Some t
  //| Some (Hon,t) -> s := {bad = true; l = (!s).l}; None
  | Some (Adv,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Hon,t))::(!s).l} ;
                    add_some t

let hash_hon k f = let s = compose2 (fun _ -> !s) (fun _ -> !s) () () in
                   let l = rel_map1 (fun s -> s.l) s in

                   (* Actual code. The rest is just to apply the correct lemmas *)
                   let r = sample #tag #tag f in
                   let t = compose2 (fun k -> hash_hon' k (R.l r))
                                   (fun k -> hash_hon' k (R.r r))
                                   (R.l k) (R.r k) in

                   good_sample_fun_bijection #tag #tag f;
                   if (not (or_rel (rel_map1 (fun s -> s.bad) s))) then
                     if and_rel (rel_map1 is_Some t) then
                       (ok_hon_safe k l;
                       ok_hon_safe2 k l;
                       if and_rel (rel_map2 (fun k l -> is_None (assoc k l)) k l) then
                         ok_consH k (R (Some.v (R.l t)) (Some.v (R.r t))) l);
                   t

let case_Hon  t     = Some t
let case_Adv  _     = s:={bad = true; l=(!s).l}; None
let case_None (k,t) = s:={bad = (!s).bad; l = (k,(Hon,t))::(!s).l}; add_some t

assume val sample_single : unit -> Tot tag

let hash_hon2 k f =
  let s = compose2 (fun _ -> !s) (fun _ -> !s) () () in
  let l = rel_map1 (fun s -> s.l) s in
  let b = or_rel (rel_map1 (fun s -> s.bad) s) in
  match rel_map2 assoc k l with
  | R (Some (Hon,t0)) (Some (Hon,t1)) -> if not b then
                                           ok_hon_safe2 k l;
                                         compose2 (fun x -> case_Hon x) (fun x -> case_Hon x) t0 t1
  | R (Some (Hon,t0)) (Some (Adv,t1)) -> compose2 (fun x -> case_Hon x) (fun x -> case_Adv x) t0 ()
  | R (Some (Hon,t0)) (None         ) -> if not b then
                                           ok_hon_safe k l;
                                         let t1 = sample_single () in
                                         compose2 (fun x -> case_Hon x) (fun x -> case_None x) t0 ((R.r k),t1)
  | R (Some (Adv,t0)) (Some (Hon,t1)) -> compose2 (fun x -> case_Adv x) (fun x -> case_Hon x) () t0
  | R (Some (Adv,t0)) (Some (Adv,t1)) -> compose2 (fun x -> case_Adv x) (fun x -> case_Adv x) () ()
  | R (Some (Adv,t0)) (None         ) -> let t1 = sample_single () in
                                         compose2 (fun x -> case_Adv x) (fun x -> case_None x) () ((R.r k),t1)
  | R (None         ) (Some (Hon,t1)) -> if not b then
                                           ok_hon_safe k l;
                                         let t0 = sample_single () in
                                         compose2 (fun x -> case_None x) (fun x -> case_Hon x) ((R.l k),t0) t1
  | R (None         ) (Some (Adv,t1)) -> let t0 = sample_single () in
                                         compose2 (fun x -> case_None x) (fun x -> case_Adv x) ((R.l k),t0) ()
  | R (None         ) (None         ) -> let t = sample #tag #tag f in
                                         good_sample_fun_bijection #tag #tag f;
                                         if not b then
                                           ok_consH k t l;
                                         compose2 (fun x -> case_None x) (fun x -> case_None x) (R.l k, R.l t) (R.r k, R.r t)
let hash_adv' k r =  match assoc k (!s).l with
  | Some (Adv,t) -> Some t
  | Some (Hon,t) -> s := {bad = true; l = (!s).l}; None
  | None         -> let t = r in
                    s := {bad = (!s).bad; l= (k,(Adv,t))::(!s).l} ;
                    add_some t


let hash_adv k  = let s = compose2 (fun _ -> !s) (fun _ -> !s) () () in
                  let l = rel_map1 (fun s -> s.l) s in

                  (* Actual code, the rest is just for calling lemmas *)
                  cut(bijection #tag #tag  (fun x -> x));
                  bijection_good_sample_fun #tag #tag (fun x -> x);
                  let r = sample (fun x->x) in
                  let t = compose2 (fun k -> hash_adv' k (R.l r))
                                   (fun k -> hash_adv' k (R.r r))
                                   (R.l k) (R.r k) in

                  if (not (or_rel (rel_map1 (fun s -> s.bad) s))) then
                    if and_rel (rel_map1 is_Some t) then
                      (ok_adv_eq k l;
                      if and_rel (rel_map2 (fun k l -> is_None (assoc k l)) k l) then
                        ok_consA k (R (Some.v (R.l t)) (Some.v (R.r t))) l);
                  t

(* Simple Encryption Scheme based on ro *)
module Encryption

open Comp
open Heap
open Bijection
open Sample
open Relational
open Xor
open Bytes
open List
open Ro


assume val append : bytes -> bytes -> Tot bytes

val encrypt : block -> block -> Tot block
let encrypt p k = xor p k
val decrypt : block -> block -> Tot block
let decrypt c k = xor c k

opaque type safe_key_pre (k:double bytes) = (forall (r:block). safe_key (rel_map2 append k (twice r)))

opaque val encrypt_good_sample_fun : p1:block -> p2:block
  -> Lemma (good_sample_fun #block #block (fun x -> xor (xor p1 p2) x))
let encrypt_good_sample_fun p1 p2 =
  let sample_fun = (fun x -> xor (xor p1 p2) x) in
  cut (bijection #block #block sample_fun);
  bijection_good_sample_fun #block #block sample_fun

opaque val id_good_sample_fun : unit -> Lemma (good_sample_fun #block #block (fun x -> x))
let id_good_sample_fun () =
  cut (bijection #block #block (fun x -> x));
  bijection_good_sample_fun #block #block (fun x -> x)

#reset-options
opaque val encrypt_hon : k:double key{safe_key_pre k}
                  -> p:double block ->
                  ST2 (double (option (block * block)))
                 (requires (fun h2 -> goodstate_hash (sel_rel h2 (twice s))))
                 (ensures (fun h2' p h2 -> goodstate_hash (sel_rel h2 (twice s))
                                           /\( not (or_rel (rel_map1 (fun s -> s.bad) (sel_rel h2 (twice s))))
                                             ==> Ok (rel_map1 (fun s -> s.l)(sel_rel h2 (twice s)))
                                             /\ is_Some (R.l p) /\ is_Some (R.r p)
                                             /\ snd (Some.v (R.l p)) = snd (Some.v (R.r p))
                                             /\ (fresh_keys (rel_map2 append k (R (snd(Some.v #(block * block) (R.l p)))
                                                                                  (snd(Some.v #(block * block) (R.r p)))))
                                                            (rel_map1 (fun s -> s.l) (sel_rel h2' (twice s)))
                                                            ==> eq_rel p))))
#reset-options
let encrypt_hon k p =
                  let sample_fun = (fun x -> xor (xor (R.l p) (R.r p)) x) in
                  id_good_sample_fun ();
                  encrypt_good_sample_fun (R.l p) (R.r p);
                  let r = sample #block #block (fun x -> x) in
                  let kh = rel_map2 append k r in

                  let h = hash_hon kh (sample_fun) in
                  (* Writing the code in this style causes the loss of some typing information *)
(*                   let c = rel_map3 (fun h p r -> if is_Some h then Some ((encrypt p (Some.v h)), r) else None) h p r in *)
                  let cl = if is_Some (R.l h) then Some ((encrypt (R.l p) (Some.v (R.l h))), (R.l r)) else None in
                  let cr = if is_Some (R.r h) then Some ((encrypt (R.r p) (Some.v (R.r h))), (R.r r)) else None in
                  let c = R cl cr in

                  c


#reset-options
opaque val decrypt_hon : k:double bytes{safe_key_pre k} ->
                  c:double(block * block){snd (R.l c) = snd (R.r c)} ->
                  ST2 (double (option block))
                 (requires (fun h2 -> goodstate_hash (sel_rel h2 (twice s))))
                 (ensures (fun h2' p h2 -> goodstate_hash (sel_rel h2 (twice s))))
let decrypt_hon k c =
                  let r = rel_map1 snd c in
                  let kh = rel_map2 append k r in
                  id_good_sample_fun ();
                  let h = hash_hon kh (fun x -> x) in
                  (* Writing the code in this style causes the loss of some typing information *)
(*                   rel_map2 (fun h c -> if is_Some h then Some (decrypt (fst c) (Some.v h)) else None) h c *)
                  let a = if is_Some (R.l h) then Some (decrypt (fst (R.l c)) (Some.v (R.l h))) else None in
                  let b = if is_Some (R.r h) then Some (decrypt (fst (R.r c)) (Some.v (R.r h))) else None in
                  R a b
