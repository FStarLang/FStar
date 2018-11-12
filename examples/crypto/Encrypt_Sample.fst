module Encrypt_Sample
open FStar.All

let plain (x:AES.plain) = x 
let repr (x:AES.plain) = x 

let test() =
  let p = failwith "nice bytes" in
  let k0 = Encrypt_SymEnc.keygen true plain repr in
  let k1 = Encrypt_SymEnc.keygen true plain repr in
  let c = Encrypt_SymEnc.encrypt k0 p in
  let p' = Encrypt_SymEnc.decrypt k0 c in
//assert( p == p');                   // this succeeds, by functional correctness
  (* let p'' = SymEnc.decrypt k1 c in  // this rightfully triggers an error *)
  ()
