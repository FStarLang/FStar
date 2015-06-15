(*--build-config
    options:--z3timeout 10 --prims ../../lib/prims.fst --verify_module MAC --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1;
    variables:LIB=../../lib;
    other-files:$LIB/string.fst $LIB/list.fst
            $LIB/ext.fst $LIB/classical.fst
            $LIB/set.fsi $LIB/set.fst
            $LIB/heap.fst $LIB/st.fst
            $LIB/seq.fsi $LIB/seqproperties.fst
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
open Seq
open Set

open ST
open Heap


type bytes = seq byte (* concrete byte arrays *)
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) =
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16
let macsize = 20

type key = nbytes keysize
type tag = nbytes macsize

assume val sample: n:nat -> nbytes n
assume val sha1: key -> text -> Tot tag


(* to verify, we simply recompute & compare *)

val sha1verify: key -> text -> tag -> Tot bool
let sha1verify k txt tag = (sha1 k txt = tag)


(* ---- specification *)

(* we attach an authenticated properties to each key,
   used as a pre-condition for MACing and
   a postcondition of MAC verification *)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

(* NB: this is part of the implementation, but we need it to specify
   the type of the interface *)

(* to model authentication, we log all genuine calls
   to MACs; the ideal implementation below uses the
   log to correct errors. *)

type entry =
  | Entry : k:key
         -> t:text{key_prop k t}
         -> m:tag
         -> entry


let log : ref (list entry) = ST.alloc []

(* end of implementation dependencies *)

(* when I generate a key with keygen I provide a property `p` about
   the text that I'm MACing.*)
val keygen: p:(text -> Type) -> pkey p
(* Before I MAC I require key_prop to hold on text. *)
val mac:    k:key -> t:text{key_prop k t} -> ST tag (requires (fun h -> contains h log))
                                                    (ensures (fun h x h' -> modifies !{ log } h h'))

(* After I verify I ensure that the key_property holds on the text *)
val verify: k:key -> t:text -> tag -> ST (b:bool{b ==> key_prop k t})
					 (requires (fun h -> True))
					 (ensures (fun h x h' -> modifies !{} h h'))

(* If MAC is secure and if I only MAC things for which the property
   holds (because it's a precondition for MACing, and only the
   protocol has the key) *)
(* A leak function that returns the key, requires that the key is
   dishonest.*)
(* val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t \/ leaked k} *)
(* this models compromise *)



(* ---- implementation *)

let keygen (p: (text -> Type)) =
  let k = sample keysize in
  assume (key_prop k == p);
  k

let mac k t =
  let m = sha1 k t in
  let l = !log in
  log:=(Entry k t m :: l);
  m

let verify k text tag =
  let verified = sha1verify k text tag in
  let found =
    is_Some
      (List.find
        (fun (Entry k' text' tag') -> k=k' && text=text')
        !log) in

  (* plain, concrete implementation (ignoring the log) *)
//verified

  (* ideal, error-correcting implementation *)
  verified && found
  (* the link between ideal and concrete is an assumption *)

  (* error-detecting implementation for the INT-CMA game *)
//(if verified && not found then win := Some(k,text,tag));
//verified
