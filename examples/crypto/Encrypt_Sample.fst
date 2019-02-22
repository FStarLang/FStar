(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
