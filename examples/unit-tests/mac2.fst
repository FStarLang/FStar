(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Seq --admit_fsi FStar.SeqProperties;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.List.fst
  --*)
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
open FStar.Seq
type bytes = seq byte (* concrete byte arrays *)
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) = b:bytes{length b = n} (* fixed-length bytes *)

let keysize = 16 (* these are the sizes for SHA1 *)
let macsize = 20
type key = nbytes keysize
type tag = nbytes macsize

(* we rely on some external crypto library implementing HMAC-SHA1 *)

assume val sha1: key -> text -> Tot tag

(* to verify, we simply recompute & compare *)

val sha1verify: key -> text -> tag -> Tot bool
let sha1verify k txt tag = (sha1 k txt = tag)

(* we attach an authenticated properties to each key,
   used as a pre-condition for MACing and
   a postcondition of MAC verification *)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

assume val leak: k:key { forall t. key_prop k t } -> bytes
assume val leaked: k:key -> b:bool { b ==> (forall t. key_prop k t) }

(* this function returns the key bytes, and marks the key as corrupted *)

assume val keygen: p:(text -> Type) -> pkey p

val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}

(* to model authentication, we log all genuine calls to MACs *)

(* the ideal implementation below uses a global log *)

type entry =
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

let log = ST.alloc #(list entry) []

let mac k t =
  let m = sha1 k t in
  log := Entry k t m :: !log;
  m

let verify k text tag =
  let verified = sha1verify k text tag in
  let found    = is_Some(List.find (function (Entry k' text' tag') -> k=k' && text=text' (*CTXT: && tag=tag' *) ) !log) in

  (* plain, concrete implementation (ignoring the log) *)
//verified

  (* ideal, error-correcting implementation *)
  verified && (found || leaked k )

  (* error-detecting implementation for the INT-CMA-LEAK game *)
//if verified && not (found || leaked k) then win:= Some(k,text,tag);
//verified
