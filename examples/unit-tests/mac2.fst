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

module MAC 
open Array
type bytes    = seq byte
type text     = bytes
type nbytes (n:nat) = b:bytes{length b == n}

let keysize = 16 (* these are the sizes for SHA1 *) 
let macsize = 20  
type key = nbytes keysize
type tag = nbytes macsize

(* we rely on some external crypto library implementing HMAC-SHA1 *)

assume val sha1: key -> text -> Tot tag 
val sha1verify: key -> text -> tag -> Tot bool
let sha1verify k txt tag = (sha1 k txt = tag)

(* we attach an authenticated properties to each key *) 

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}


assume val leak: k:key { forall t. key_prop k t } -> bytes 
assume val leaked: k:key -> b:bool { b ==> (forall t. key_prop k t) }   // TODO why do I need parentheses?

(* this function returns the key bytes, and marks the key as corrupted *)

(* TODO make keys abstract except within this module *) 

assume val keygen: p:(text -> Type) -> pkey p

(* to model authentication, we log all genuine calls to MACs *) 

val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}


(* the ideal implementation below uses a global log *)

(* TODO provide a concrete implementation of keygen, aka sample 16
   random bytes + maybe a counter it would be better to avoid assuming
   key_prop; see also encrypt.fst *)

type entry = 
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

(* TODO why assumed? we miss toplevel side effects... *) 

assume val log : ref (list entry)

let mac k t = 
  let m = sha1 k t in
  log := Entry k t m :: !log;
  m

let verify k text tag =
  let verified = sha1verify k text tag in 
  let found    = is_Some(List.find (function (Entry k' text' tag') -> k=k' && text=text' (*CTXT: && tag=tag' *) ) !log) in 
//verified           (* concrete: we never read the log *) 
  verified && (found || leaked k ) (* ideal: we correct errors. *)
//(if verified && not (found || leaked k) then winner:= Some(k,text,tag)) verified (* winning condition against for INT-CPA *)

(* VARIANT CTXT vs CPA: is the tag authenticated? 
   otherwise do not include m:tag in the entry *)
