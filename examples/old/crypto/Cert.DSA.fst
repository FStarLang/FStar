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
module Cert.DSA 
open Array

type bytes = seq byte (* concrete byte arrays *) 
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) = 
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing the DSA standard *)

let keysize = 256 
let tagsize = 20  

type vk = nbytes keysize
type sk = nbytes keysize
assume val sk2vk  : sk -> Tot vk
assume val keygen : unit -> sk

type tag = nbytes tagsize

assume val sign   : sk -> text -> tag 
assume val verify : vk -> text -> tag -> Tot bool 


