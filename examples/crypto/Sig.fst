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

module Sig

open FStar.Array
open FStar.List.Tot
open FStar.All
open FStar.ST
open Platform.Bytes

type text     = bytes
let sigsize = 256
let sksize = 256
let pksize = 256
type sig_t = lbytes sigsize
type pk   = lbytes pksize
type sk   = lbytes sksize

assume val fdh_rsa: sk -> text -> Tot sig_t

assume val key_prop : pk -> text -> Type0
type prop_pk (p:(text -> Type)) = k:pk{key_prop k == p}

assume val sk_to_pk : sk -> Tot pk


type pk_sk (p:pk) = s:sk{sk_to_pk s == p}

assume val keygen: p:(text -> Type) -> k:prop_pk p & pk_sk k

type entry =
  | Entry : k:pk
         -> t:text{key_prop k t}
         -> m:sig_t
         -> entry

assume val log : ref (list entry)

val sign: p:pk
      -> s:pk_sk p
      -> t:text{key_prop p t}
      -> ML sig_t
let sign p s t =
  let m = fdh_rsa s t in
  log := Entry p t m :: !log;
  m

val verify: p:pk
         -> t:text
         -> sig_t
         -> ML (b:bool{b ==> key_prop p t})
let verify p t m =
  let found = List.Tot.find (function (Entry p' t' _) -> p=p' && t=t') !log in
  Some? found
