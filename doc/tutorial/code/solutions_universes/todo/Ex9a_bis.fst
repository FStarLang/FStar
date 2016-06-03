(* to be used with mac.fst and acls2.fst *)

module Ex9a_bis (* capabilities *) 
open FStar.Array
open Ex9a_quar
open Ex9a_ter
open Ex9bc

module ACLs = Ex9a
module SHA1 = Ex9a_quar
module MAC = Ex9bc

assume val utf8: s:string  -> Tot (seq byte) 

(*
assume UTF8_inj: 
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    equal (utf8 s0) (utf8 s1) ==> s0==s1

type capRead (msg:seq byte) = (forall f. msg = utf8 f ==> ACLs.canRead f)

let k = keygen capRead

val issue: f:file{ canRead f } -> SHA1.tag 
val redeem: f:file -> m:SHA1.tag -> u:unit{ canRead f }

let issue f = MAC.mac k (utf8 f)
let redeem f t = if MAC.verify k (utf8 f) t then () else failwith "bad capability"
