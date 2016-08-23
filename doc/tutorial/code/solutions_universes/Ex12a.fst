(* to be used with mac.fst and acls2.fst *)

module Ex12a (* capabilities *) 
open FStar.Array
open FStar.Bytes
open FStar.Seq


module ACLs = Ex12a_ACLs
//module SHA1 = Ex9a_quar
module MAC = Ex12a_MAC

assume val utf8: s:string  -> Tot (seq byte) 


assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    equal (utf8 s0) (utf8 s1) ==> s0==s1


type capRead (msg:seq byte) = (forall f. msg = utf8 f ==> ACLs.canRead f)

let k = MAC.keygen capRead


val issue: f:string{ ACLs.canRead f } -> MAC.tag

val redeem: f:string -> m:MAC.tag -> u:unit{ ACLs.canRead f }


let issue f = 
  assert(ACLs.canRead f);
  let bs = (utf8 f) in
  assert(capRead bs);
  assume(MAC.key_prop k bs);
  MAC.mac k bs


let redeem f t = 
  let bs = (utf8 f) in
  if MAC.verify k bs t then 
    (
    assume(capRead bs);
    ()
    )
  else 
    failwith "bad capability"
    
