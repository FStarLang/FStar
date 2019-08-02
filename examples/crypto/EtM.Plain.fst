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
module EtM.Plain

open Platform.Bytes
open CoreCrypto
open EtM.Ideal

abstract 
type plain : eqtype = bytes

abstract
let reveal (p:plain) : GTot bytes = p

abstract
let hide (b:bytes) : GTot plain = b

let reveal_hide (p:plain) 
  : Lemma (hide (reveal p) == p)
          [SMTPat (reveal p)]
  = ()

let hide_reveal (b:bytes) 
  : Lemma (reveal (hide b) == b)
          [SMTPat (hide b)]
  = ()

abstract
let repr (p:plain{not conf}) 
  : (b:bytes{b == reveal p}) 
  = p

abstract
let coerce (r:bytes{not auth}) 
  : (p:plain{p == hide r}) 
  = r

module B = Platform.Bytes
abstract
let length (p:plain) 
  : (n:nat{n = B.length (reveal p)})
  = B.length p
