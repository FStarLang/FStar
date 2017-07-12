(* This file implements message authentication codes based on keyed
   hashes, namely HMAC-SHA1, and their idealization under the INT-CMA
   computational assumption *)

module Ex12.MAC

(* open FStar.HyperStack.ST *)
(* open FStar.HyperStack.All *)
(* open FStar.Seq *)
(* open FStar.Monotonic.Seq *)
(* open FStar.HyperHeap *)
(* open FStar.HyperStack *)
(* open FStar.Monotonic.RRef *)


open Ex12.SHA1
open FStar.IO
module SEM = FStar.StrongExcludedMiddle
open FStar.Classical
open FStar.Squash
(* open FStar.PredicateExtensionality *)

open Preorder
open Heapx
open STx
open Allx
open MRefx

module SHA1 = Ex12.SHA1
open FStar.List.Tot

(* key log *)
let unique_registry_order' (#a:eqtype) (#b:Type) (l1 l2:list (a * b))
  = (forall x. x `memP` l1 ==> x `memP` l2) /\ (noRepeats (map fst l1) ==> noRepeats (map fst l2))
let unique_registry_order (#a:eqtype) (#b:Type) : Tot (preorder (l:list (a * b))) =
  unique_registry_order' #a #b




(* let rec noRepeatsP (#a:Type) (l:list a) = *)
(*   match l with *)
(*   | [] -> True *)
(*   | x :: xs -> ~(x `memP` xs) /\ noRepeatsP xs *)
(*   (\* let fold_fun x (fml, suffix) = (fml /\ ~(x `memP` suffix)), x :: suffix in *\) *)
(*   (\* fst (fold_right fold_fun l (True, [])) *\) *)

(* let noRepeatsP_cons (#a:Type) (l:list a{noRepeatsP l}) (x:a{~(x `memP` l)}) *)
(*   : (l:list a{noRepeatsP l}) *)
(* = x :: l *)

let dec_ghost_to_pred (#a:Type) (p:a -> GTot bool)
  : a -> Tot Type0 (* prop *)
= fun x -> b2t (p x)

let pred_to_dec_ghost (#a:Type) (p:a -> Tot Type0 (* prop *))
  : a -> GTot bool
= fun x -> SEM.strong_excluded_middle (p x)

(* let lemma_dec_ghost_pred_id (#a:Type) (p: a -> Type0) *)
(*   : Lemma (dec_ghost_to_pred (pred_to_dec_ghost p) `feq` p) *)
(* = () *)
(* ---- specification *)


(* We make the MAC.key abstract so that it cannot be accessed by
    the adversary *)

abstract type key = SHA1.key
type key_entry = key * (text -> GTot bool)
type key_lref = mref (l:list key_entry) unique_registry_order
let unicity ()
  : Tot (p:(l:list key_entry -> Type0){Preorder.stable p (unique_registry_order)})
= fun keys -> noRepeats (map fst keys)

let key_log : lr:key_lref{token lr (unicity ())} =
  let lr = alloc _ [] in
  witness lr (unicity ()) ;
  lr

let associated_to' (k:key) (p:text -> GTot bool)  =
  fun keys -> (k,p) `memP` keys
let associated_to k p
  : Tot (p:(l:list key_entry -> Type0){Preorder.stable p (unique_registry_order)})
= associated_to' k p

(* we attach an authenticated properties to each key,
   used as a pre-condition for MACing and
   a postcondition of MAC verification *)
type pkey (p:text -> Type) = k:key{token key_log (associated_to k (pred_to_dec_ghost p))}

let key_prop k t =  exists p. token key_log (associated_to k p) /\ p t

let exists_stable0 rel p (w : squash (forall x. Preorder.stable (p x) rel)) y1 y2 : Lemma (requires (exists x. p x y1) /\ y1 `rel` y2) (ensures (exists x. p x y2)) = give_proof w
let exists_stable rel p : Lemma (requires (forall x. Preorder.stable (p x) rel))
    (ensures (Preorder.stable (fun y -> exists x. p x y) rel))
=
  forall_intro_2 (fun y1 y2 ->
    move_requires (exists_stable0 rel p (get_proof (forall x. Preorder.stable (p x) rel)) y1) y2
    <: Lemma ((exists x. p x y1) /\ y1 `rel` y2 ==> (exists x. p x y2)))

let thing0 k t = fun x -> exists (p:text -> GTot bool). associated_to k p x /\ p t
let thing k t : spred unique_registry_order = exists_stable unique_registry_order (fun p x -> associated_to k p x /\ p t) ; thing0 k t
let lemma_thing k t x : Lemma (thing k t x == (exists (p:text -> GTot bool). associated_to k p x /\ p t)) = ()
let lemma_thing' k t x : Lemma (thing k t x <==> (exists (p:text -> GTot bool). associated_to k p x /\ p t)) = lemma_thing k t x ; assert (thing k t x <==> thing k t x)
let stuff k t : Lemma (requires (key_prop k t)) (ensures (token key_log (thing k t))) =
  let aux p : Lemma (requires (token key_log (associated_to k p) /\ p t))
              (ensures (token key_log (thing k t))) =
    MRefx.lemma_functoriality key_log (associated_to k p) (thing k t)
  in
  forall_to_exists (fun p -> move_requires aux p <: Lemma (token key_log (associated_to k p) /\ p t ==> token key_log (thing k t)))

let panda #rel (p q : spred rel) = fun x -> p x /\ q x
let pand #rel (p q : spred rel) : spred rel = panda p q

let token_intro_and #a #rel (r:mref a rel) (p q : spred rel)
  : ST unit (requires (fun _ -> token r p /\ token r q))
    (ensures (fun _ _ _ -> token r (pand p q)))
= recall r p ; recall r q ; witness r(pand p q)

let rec mem_assoc_unique (#a:eqtype) (#b:Type) (x:a) (l:list (a * b)) (y1 y2:b)
  : Lemma (requires ((x, y1) `memP` l /\ (x,y2) `memP` l /\ noRepeats (map fst l)))
          (ensures (y1 == y2))
= match l with
  | [] -> ()
  | x0 :: xs ->
    if x = fst x0 then begin
        mem_memP x (map fst xs) ;
        memP_map_intro fst (x, y1) xs ;
        memP_map_intro fst (x,y2) xs
      end
    else
      mem_assoc_unique x xs y1 y2

let key_prop_unicity (k:key) (p:text -> GTot bool) (t:text) keys
 : Lemma
  (requires ((unicity () `pand` (associated_to k p `pand` thing k t)) keys))
  (ensures (p t))
  =
  let aux p' : Lemma (requires associated_to k p' keys /\ p' t) (ensures p t) =
    mem_assoc_unique k keys p p'
  in
  assert (thing k t keys) ;
  lemma_thing k t keys ;
  assert( exists p. associated_to k p keys /\ p t ) ;
  admit () ;
  forall_to_exists (move_requires aux)

let key_prop_unicity' (k:key) (p:text -> GTot bool) (t:text)
  : Lemma (forall keys. (unicity () `pand` (associated_to k p `pand` thing k t)) keys ==> p t)
= forall_intro (move_requires (key_prop_unicity k p t))

(* let key_prop_unicity (k:key) (p p' : text -> GTot bool) *)
(*   : ST unit *)
(*     (requires (fun _ -> *)
(*       token key_log (associated_to k p) /\ *)
(*       token key_log (associated_to k p'))) *)
(*     (ensures (fun _ _ _ -> p == p')) *)
(* = recall key_log (unicity ()) ; *)
(*   recall key_log (associated_to k p) ; *)
(*   recall key_log (associated_to k p') ; *)
(*   mem_assoc_unique k !key_log p p' *)

(* let key_prop_unicity' (k:key) (p p' : text -> GTot bool) *)
(*   : ST unit *)
(*   (requires (fun _ -> True)) *)
(*   (ensures (fun _ _ _ -> token key_log (associated_to k p) /\ token key_log (associated_to k p') ==> p == p')) *)
(* = key_prop_unicity k p p' *)

let to_key_prop #p (k:pkey p) : Lemma (forall x. p x ==> key_prop k x) = ()
let from_key_prop #p (k:pkey p) t : ST unit (requires (fun _ -> key_prop k t)) (ensures (fun _ _ _ -> p t)) =
  stuff k t ;
  let p = pred_to_dec_ghost p in
  token_intro_and key_log (associated_to k p) (thing k t) ;
  token_intro_and key_log (unicity ()) (associated_to k p `pand` thing k t) ;
  key_prop_unicity' k p t ;
  lemma_functoriality key_log (unicity () `pand` (associated_to k p `pand` thing k t)) (fun _ -> p t) ;
  admit ()


  recall key_log (p t)

(* to model authentication, we log all genuine calls
   to MACs; the ideal implementation below uses the
   log to correct errors. *)

type tag = SHA1.tag

type entry =
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

(* the log needs to be private so the adversary cannot
   add or remove entries *)


private type log_t = ref (list entry)
let log:log_t = STx.alloc _ []


// BEGIN: MacSpec
val keygen: p:(text -> Type0) -> ML (pkey p)
val mac:    k:key -> t:text{key_prop k t} -> ST tag
  (requires (fun h -> True))
  (ensures (fun h x h' -> modifies (Set.singleton (addr_of log)) h h'))
val verify: k:key -> t:text -> tag -> ST (b:bool{b ==> key_prop k t})
  (requires (fun h -> True))
  (ensures (fun h x h' -> modifies Set.empty h h'))
// END: MacSpec

(* ---- implementation *)

let keygen (p: (text -> Type)) =
  let p = pred_to_dec_ghost p in
  let k:key = sample keysize in
  if k `mem` map fst !key_log
  then failwith "Not a valid key"
  else begin
    key_log := (k,p) :: !key_log ;
    witness key_log (associated_to k p) ;
    k
  end

let mac k t =
  let m = hmac_sha1 k t in
  log := Entry k t m :: !log;
  m

let verify k text tag =
  (* to verify, we simply recompute & compare *)
  let m= hmac_sha1 k text in
  let verified = (Platform.Bytes.equalBytes m tag) in
  let found =
    Some?
      (List.Tot.find
        (fun (Entry k' text' tag') -> Platform.Bytes.equalBytes k k' && Platform.Bytes.equalBytes text text')
        !log) in

  (* plain, concrete implementation (ignoring the log) *)
//verified

  (* ideal, error-correcting implementation *)
  verified && found
//  found

  (* error-detecting implementation for the INT-CMA game *)
//(if verified && not found then win := Some(k,text,tag));
//verified

(* VARIANT CTXT vs CPA: is the tag authenticated?
   otherwise do not include m:tag in the entry *)

//      (fun (Entry k' text' tag') -> k=k' && text=text' && tag=tag')
