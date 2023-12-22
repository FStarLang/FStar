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
module Hybrid
open Array
open PKE

(* we idealize first PKE, then SymEnc *)

let pksize = PKE.pksize
let ciphersize = PKE.ciphersize + SymEnc.ciphersize
 
let enc t = 
  let k = SymEnc.keygen true in 
  append 
    (PKE.encrypt pk k) 
    (SymEnc.encrypt k t)

let dec c =
  let c0,c1 = split c PKE.ciphersize in 
  SymEnc.decrypt (PKE.decrypt sk c0) c1 

// let keygen() = PKE.keygen 
