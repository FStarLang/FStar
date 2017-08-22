(* to be used with Ex12.MAC.fst and Ex12a.ACLs.fst *)

module Ex12a1.Cap (* capabilities *)

open FStar.ST
open FStar.All
open Platform.Bytes


module ACLs = Ex12a.ACLs
module MAC = Ex12.MAC

// BEGIN: UTF8Inj
assume val utf8: s:string  -> Tot bytes

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
     b2t (equalBytes (utf8 s0) (utf8 s1)) ==> s0==s1
// END: UTF8Inj

type capRead (msg:bytes) = (forall f. msg = utf8 f ==> ACLs.canRead f)

let k = MAC.keygen capRead

// BEGIN: CapType
val issue: f:string{ ACLs.canRead f } -> ML MAC.tag
val redeem: f:string -> m:MAC.tag -> ML (u:unit{ ACLs.canRead f })
// END: CapType

let issue f = failwith "Implement this function"
let redeem f t = failwith "Implement this function"
