module Cap (* capabilities *)
open FStar.ST
open FStar.Seq
open FStar.String
open Cert.ACLs
open MAC


type byte = Platform.Bytes.byte

assume val utf8: s:string  -> Tot (seq byte)

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    (utf8 s0) == (utf8 s1) ==> s0==s1

type capRead (msg:seq byte) =
    (forall f. msg = utf8 f ==> canRead f)

let gen () = keygen capRead

let issue (f:file{ canRead f }) (k:pkey capRead) = MAC.mac k (utf8 f)

//val redeem: f:file -> m:SHA1.tag -> pkey capRead -> St (option (u:unit{ canRead f }))
let redeem f t k = 
  if MAC.verify k (utf8 f) t then 
    Some ()
  else 
    None

let f = "C:/public/README"
  
let main () : St (u:unit{ canRead f }) =
  let k = gen () in
  let t = issue f k in  
  Some?.v (redeem f t k)
  
