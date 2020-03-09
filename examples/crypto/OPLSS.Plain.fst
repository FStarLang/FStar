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
module OPLSS.Plain
open OPLSS
open OPLSS.Ideal

abstract 
type plain : eqtype = AES.plain

abstract
let reveal (p:plain) : GTot AES.plain = p

abstract
let hide (b:AES.plain) : GTot plain = b

let reveal_hide (p:plain) 
  : Lemma (hide (reveal p) == p)
          [SMTPat (reveal p)]
  = ()

let hide_reveal (b:AES.plain)
  : Lemma (reveal (hide b) == b)
          [SMTPat (hide b)]
  = ()

abstract
let repr (p:plain{not (Flag.reveal conf)}) 
  : (b:AES.plain{b == reveal p}) 
  = p

abstract
let coerce (r:AES.plain{not (Flag.reveal auth)}) 
  : (p:plain{p == hide r}) 
  = r

abstract
let length (p:plain) 
  : (n:nat{n = Seq.length (reveal p)})
  = Seq.length p
