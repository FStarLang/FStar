module HyE.PlainPKE

open Platform.Bytes
open HyE.RSA
open HyE.Flags
open HyE.AE
open HyE.PlainAE
open HyE.Indexing
open FStar.HyperHeap
open FStar.HyperStack
open FStar.Monotonic.RRef


type protected_pke_plain = HyE.AE.key // This works because HyE.AE.key is abstract
assume Plain_hasEq: hasEq protected_pke_plain
type pke_plain = aes_key 

(* two pure functions, never called when ideal *)
val repr: p:protected_pke_plain{not pke_ind_cca} -> Tot pke_plain
let repr p = HyE.AE.leak p       (* a pure function from t to RSA.plain *)

val coerce: i:id{not (honest i)} -> parent:rid -> x:pke_plain -> ST (option (y:HyE.AE.key)) 
  (requires (fun h0 -> True))
  (ensures (fun h0 _ h1 -> True))
let coerce i parent x = Some (HyE.AE.coerce_key i parent x ) (* a partial function from RSA.plain to HyE.AE.key *)
