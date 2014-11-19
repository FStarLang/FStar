(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module MacIdeal 
type bytes    = list byte
type text     = bytes
type nbytes (n:nat) = b:bytes{List.length b == n}
let macsize = 20
let keysize = 16
type mac_t = nbytes macsize
type key   = nbytes keysize
assume val hmac_sha1: key -> text -> Tot mac_t

type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

assume val new_key: p:(text -> Type) -> pkey p

type entry = 
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:mac_t
         -> entry

assume val log : ref (list entry)

val mac: k:key
      -> t:text{key_prop k t}
      -> mac_t
let mac k t = 
  let m = hmac_sha1 k t in
  log := Entry k t m :: !log;
  m

val verify: k:key
         -> t:text 
         -> mac_t 
         -> b:bool{b ==> key_prop k t}
let verify k t m = 
  let found = List.find (function (Entry k' t' _) -> k=k' && t=t') !log in
  is_Some found

