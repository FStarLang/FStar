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
module Flag
open Crypto.Indexing

(* Settings *all* flags to false, for extracting real implementation *) 

//16-10-08 removing any inline here as they seem incompatible with interfaces

let cipher_prf  a = false 
let mac_log       = false
let mac_int1cma a = false 
let prf_cpa       = false  
let safeHS      i = false 
let safeId      i = false 
let mac1_implies_mac_log i = ()
let mac1_implies_prf     i = ()
let safeId_implies_mac1  i = ()
let safeId_implies_cpa   i = ()
let aes_ct        = false
