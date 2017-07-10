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

open Preorder
open Heapx
open STx
open MRefx

module SHA1 = Ex12.SHA1
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


(* ---- specification *)


(* We make the MAC.key abstract so that it cannot be accessed by
   the adversary *)

abstract type key=SHA1.key

(* we attach an authenticated properties to each key,
   used as a pre-condition for MACing and
   a postcondition of MAC verification *)

assume type key_prop : key -> text -> Type0
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

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

(* let key_prop k t =  exists p. token key_log (associated_to k p) /\ p t *)

private type log_t = ref (list entry)
let log:log_t = STx.alloc _ []

// BEGIN: MacSpec
val keygen: p:(text -> Type) -> St (pkey p)
val mac:    k:key -> t:text{key_prop k t} -> ST tag 
  (requires (fun h -> True)) 
  (ensures (fun h x h' -> modifies (Set.singleton (addr_of log)) h h'))
val verify: k:key -> t:text -> tag -> ST (b:bool{b ==> key_prop k t}) 
  (requires (fun h -> True)) 
  (ensures (fun h x h' -> modifies Set.empty h h'))
// END: MacSpec

(* ---- implementation *)

let keygen (p: (text -> Type)) =
  let k:key = sample keysize in
  assume (key_prop k == p);
  k


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
