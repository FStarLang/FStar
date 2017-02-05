(**
   TODO: Documentation and some cleaup.
*)
module Box.PlainPKAE

open Box.Flags
open Box.Indexing
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef
open Platform.Bytes


abstract type protected_pkae_plain = 
  | Prot_pkae_p: #i:ae_id -> b:bytes -> protected_pkae_plain
//assume Plain_hasEq: hasEq protected_pkae_plain
type pkae_plain = bytes

val get_index: p:protected_pkae_plain -> Tot (i:ae_id{i=p.i})
let get_index p =
  p.i

(* two pure functions, never called when ideal *)
val repr: p:protected_pkae_plain{not pkae \/ ~(ae_honest p.i) } -> Tot pkae_plain
let repr p = p.b

// Change this if we want to use signcryption with pkae_int-ctxt
val coerce: #i:ae_id -> p:pkae_plain{not pkae \/ ~(ae_honest i)} -> Tot (prot:protected_pkae_plain{i=prot.i})
let coerce #i p = 
  Prot_pkae_p #i p  

val length: #i:ae_id -> protected_pkae_plain -> Tot nat
let length #i p = length p.b

// Create coece_keyshare function
