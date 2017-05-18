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

(* This file implements message authentication codes based on keyed
   hashes, namely HMAC-SHA1, and their idealization under the INT-CMA
   computational assumption *)

module MAC
//open Array
open SHA1
open FStar.IO

(* ---- specification *)

(* we attach an authenticated properties to each key,
   used as a pre-condition for MACing and
   a postcondition of MAC verification *)

assume type key_prop : key -> text -> Type0
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

(* to model authentication, we log all genuine calls
   to MACs; the ideal implementation below uses the
   log to correct errors. *)

type entry =
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

let log = ST.alloc #(list entry) []

val keygen: p:(text -> Type) -> St (pkey p)
val mac:    k:key -> t:text{key_prop k t} -> ST tag 
  (requires (fun h -> True)) 
  (ensures (fun h x h' -> 
     x == hmac_sha1 k t /\
     Heap.modifies (Heap.only log) h h' /\
     Some?
      (List.Tot.find
        (fun (Entry k' text' _) -> Platform.Bytes.equalBytes k k' && Platform.Bytes.equalBytes t text')
        (Heap.sel h' log))))
        
val verify: k:key -> t:text -> tag:tag -> ST (b:bool{b ==> key_prop k t}) 
  (requires (fun h -> True)) 
  (ensures (fun h b h' -> 
    h == h' /\
    (let verified = Platform.Bytes.equalBytes (hmac_sha1 k t) tag in
     let found =
       Some?
         (List.Tot.find 
           (fun (Entry k' text' _) ->
             Platform.Bytes.equalBytes k k' && Platform.Bytes.equalBytes t text')
           (Heap.sel h log)) in
     b == (verified && found))))
    
(* ---- implementation *)

let keygen (p: (text -> Type)) =
  let k = sample keysize in
  assume (key_prop k == p);
  k

let mac k t =
  let m = hmac_sha1 k t in
  ST.recall log;  //upd guarantees modifies singleton, only if the modified reference is contained in the heap
  log := Entry k t m :: !log;
  m

let verify k text tag =
  (* to verify, we simply recompute & compare *)
  let m = hmac_sha1 k text in
  let verified = (Platform.Bytes.equalBytes m tag) in
  let found =
    Some?
      (List.Tot.find
        (fun (Entry k' text' _) -> Platform.Bytes.equalBytes k k' && Platform.Bytes.equalBytes text text')
        !log) in

  (* plain, concrete implementation (ignoring the log) *)
//verified

  (* ideal, error-correcting implementation *)
  verified && found
//  found

  (* error-detecting implementation for the INT-CMA game *)
//(if verified && not found then win := Some(k,text,tag));
//verified

(* VARIANT CTXT vs CPA: is the tag authenticated?
   otherwise do not include m:tag in the entry *)

//      (fun (Entry k' text' tag') -> k=k' && text=text' && tag=tag')
