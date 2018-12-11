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
(* to be used with Ex12.MAC.fst and Ex12a.ACLs.fst *)

module Ex12a2.Cap (* capabilities *) 
open FStar.ST
open FStar.All
open Platform.Bytes



module ACLs = Ex12a.ACLs
module MAC = Ex12.MAC

// In Platform.Bytes: val utf8: s:string  -> Tot bytes

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
     b2t (equalBytes (utf8 s0) (utf8 s1)) ==> s0==s1

type capRead (msg:bytes) = (forall f. msg = utf8 f ==> ACLs.canRead f)

let k_read = MAC.keygen capRead

val issue_read: f:string{ ACLs.canRead f } -> ML MAC.tag
val redeem_read: f:string -> m:MAC.tag -> ML (u:unit{ ACLs.canRead f })

let issue_read f =
  assert(ACLs.canRead f);
  let bs = (utf8 f) in
  assert(capRead bs);
  MAC.mac k_read bs

let redeem_read f t =
  let bs = (utf8 f) in
  if MAC.verify k_read bs t then
    (MAC.from_key_prop k_read bs ;
    assert (ACLs.canRead f))
  else
    failwith "bad capability"

// Begin: CapImplementation2
type capWrite (msg:bytes) = (forall f. msg = utf8 f ==> ACLs.canWrite f)

let k_write = MAC.keygen capWrite

val issue_write: f:string{ ACLs.canWrite f } -> ML MAC.tag
val redeem_write: f:string -> m:MAC.tag -> ML(u:unit{ ACLs.canWrite f })

let issue_write f =
  assert(ACLs.canWrite f);
  let bs = (utf8 f) in
  assert(capWrite bs);
  MAC.mac k_write bs


let redeem_write f t =
  let bs = (utf8 f) in
  if MAC.verify k_write bs t then
    (MAC.from_key_prop k_write bs ;
    assert(ACLs.canWrite f))
  else
    failwith "bad capability"
// END: CapImplementation2
