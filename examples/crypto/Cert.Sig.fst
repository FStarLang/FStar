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
module Cert.Sig
open Array
open ST 

(* ---- specification *)

(* we attach an authenticated properties to each key, 
   used as a pre-condition for MACing and 
   a postcondition of MAC verification *)

type text = DSA.text
type tag = DSA.tag

type vk = DSA.vk
type sk = 
    | SK : DSA.sk -> sk // abstract 

val sk2vk: sk -> Tot vk
let sk2vk (SK sk) = DSA.sk2vk sk 

opaque type verified : vk -> text -> Type
type vkey (p:(text -> Type)) = k:vk{verified k == p}
type skey (p:(text -> Type)) = k:sk{verified (sk2vk k) == p}

val keygen: p:(text -> Type) -> skey p   
val sign:   p:(text -> Type) -> skey p -> t:text{p t} -> DSA.tag
val verify: p:(text -> Type) -> vkey p -> t:text -> tag -> b:bool{b ==> p t}

(* ---- implementation *)

let keygen (p: (text -> Type)) = 
  let sk = DSA.keygen() in
  let vk = DSA.sk2vk sk in
  assume (verified vk == p);
  SK sk
  
(* to model authentication, we log all genuine calls 
   to MACs; the ideal implementation below uses the 
   log to correct errors. *)

type entry = 
  | Entry : k: vk
         -> t:text{verified k t}
         -> entry

let log = ST.alloc (list entry) [] 

let sign (SK sk) text = 
  log := Entry (DSA.sk2vk sk) text :: !log;
  let tag = DSA.sign sk text in
  tag

let verify vk text tag =
  let verified = DSA.verify vk text tag in 
  let found =
    Some? 
      (List.find 
        (fun (Entry k text') -> k=vk && text=text')
        !log) in 

  (* plain, concrete implementation (ignoring the log) *) 
//verified           

  (* ideal, error-correcting implementation *) 
  verified && found  

  (* error-detecting implementation for the INT-CMA game *)
//(if verified && not found then win := Some(vk,text,tag)); 
