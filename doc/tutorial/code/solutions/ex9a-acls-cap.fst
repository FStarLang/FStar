(* to be used with mac.fst and acls2.fst *)

module Cap (* capabilities *) 
open Array
open ACLs
open MAC 

assume val utf8: s:string  -> Tot (seq byte) 

assume UTF8_inj: 
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    Equal (utf8 s0) (utf8 s1) ==> s0==s1

opaque logic type CapRead (msg:seq byte) =
    (forall f. msg = utf8 f ==> ACLs.canRead f)

let k = keygen CapRead

val issue: f:file{ canRead f } -> SHA1.tag 
val redeem: f:file -> m:SHA1.tag -> u:unit{ canRead f }

let issue f = MAC.mac k (utf8 f)
let redeem f t = if MAC.verify k (utf8 f) t then () else failwith "bad capability"
