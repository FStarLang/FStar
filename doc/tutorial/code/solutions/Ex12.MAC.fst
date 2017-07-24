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

open FStar.Preorder
open FStar.Heap
open FStar.ST
open FStar.MRef

module SHA1 = Ex12.SHA1
module SEM = FStar.StrongExcludedMiddle
(* open FStar.List.Tot *)

(* (\* key log *\) *)
(* let subset' (#a:Type) (l1:list a) (l2:list a) *)
(*   = (forall x. x `memP` l1 ==> x `memP` l2) *)
(* let subset (#a:Type) : Tot (preorder (list a)) = subset' *)

(* type key_entry = key * (string -> GTot bool) *)
(* type key_lref = mref (list key_entry) subset *)

(* let key_log : key_lref = alloc _ [] *)

(* let associated_to' (k:key) (p:string -> GTot bool)  = *)
(*   fun keys -> (k,p) `memP` keys *)

(* let associated_to k p :  Tot (p:(list key_entry -> Type0){Preorder.stable p subset}) = *)
(*   associated_to' k p *)

(* type pkey (p:string -> GTot bool) = k:key{token key_log (associated_to k p)} *)

let pred_to_dec_ghost (#a:Type) (p:a -> Tot Type0 (* prop *))
  : a -> GTot bool
= fun x -> SEM.strong_excluded_middle (p x)

(* ---- specification *)


(* We make the MAC.key abstract so that it cannot be accessed by
   the adversary *)

abstract type key= SHA1.key * (text -> GTot bool)
assume private val key_unicity (k1 k2 : key) : Lemma (requires (fst k1 == fst k2)) (ensures (snd k1 == snd k2))

(* we attach an authenticated properties to each key,
   used as a pre-condition for MACing and
   a postcondition of MAC verification *)

let key_prop : key -> text -> Type0 = fun k t -> snd k t
type pkey (p:(text -> Type)) = k:key{forall x. key_prop k x <==> p x}

(* to model authentication, we log all genuine calls
   to MACs; the ideal implementation below uses the
   log to correct errors. *)

type tag = SHA1.tag

noeq
type entry =
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

(* the log needs to be private so the adversary cannot
   add or remove entries *)

(* let key_prop k t =  exists p. token key_log (associated_to k p) /\ p t *)

private type log_t = ref (list entry)
let log:log_t = FStar.ST.alloc []

// BEGIN: MacSpec
val keygen: p:(text -> Type0) -> St (pkey p)
val mac:    k:key -> t:text{key_prop k t} -> ST tag
  (requires (fun h -> True))
  (ensures (fun h x h' -> modifies (Set.singleton (addr_of log)) h h'))
val verify: k:key -> t:text -> tag -> ST (b:bool{b ==> key_prop k t})
  (requires (fun h -> True))
  (ensures (fun h x h' -> modifies Set.empty h h'))
// END: MacSpec

(* ---- implementation *)

let keygen (p: (text -> Type)) =
  let k:key = sample keysize, pred_to_dec_ghost p in
  assert (forall x. key_prop k x <==> p x);
  k


let mac k t =
  let m = hmac_sha1 (fst k) t in
  log := Entry k t m :: !log;
  m

let verify k text tag =
  (* to verify, we simply recompute & compare *)
  let m = hmac_sha1 (fst k) text in
  let verified = (Platform.Bytes.equalBytes m tag) in
  let equal_entry (Entry k' text' tag') =
    Platform.Bytes.equalBytes (fst k) (fst k') && Platform.Bytes.equalBytes text text'
  in
  let entry_opt = List.Tot.find equal_entry !log in
  let found = Some? entry_opt in
  begin match entry_opt with
    | None -> ()
    | Some (Entry k' _ _) -> key_unicity k k'
  end ;

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
