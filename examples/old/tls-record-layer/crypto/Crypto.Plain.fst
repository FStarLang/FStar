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
module Crypto.Plain

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open Crypto.Symmetric.Bytes

// Abstraction for secret plaintexts (heap- and stack-based)

// For now we assume public lengths and no padding
// For TLS, we will pass around instead 
// - a public maximal length
// - a private actual length
// - a buffer of maximal length (possibly + 1 for TLS CT)
// The need to pass two lengths is a small price to pay for length hiding. 
// It is yet unclear whether to use buffers or bytes values. 

// Type abstraction protects against aliasing inasmuch
// as it is enforced from allocation.

open Crypto.Indexing
open Flag 

// -----------------------------------------------------------------------------

type plainLen = nat // we'll need a tigher bound

abstract type plain (i:id) (l:plainLen) = lbytes l

// ghost
val as_bytes: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)
let as_bytes #i #l p = p

// restricted
val repr: #i:id {~(safeId i)} -> #l:plainLen -> p:plain i l -> Tot (b:lbytes l {b = as_bytes p })
let repr #i #l p = p

val make: #i:id {~(safeId i)}-> l:plainLen -> b:lbytes l -> Tot (p:plain i l {b = as_bytes p})
let make #i l b = b


(*
val reveal: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)
let reveal #i #l p = p

val repr_injective : i:id -> l:plainLen -> p:plain i l -> Lemma
  (requires True)
  (ensures (make #i l (as_bytes p) == p))
  [SMTPat (as_bytes p)]
let repr_injective i l p = ()
*)

val slice: #i:id -> #l:plainLen -> p:plain i l -> s:nat -> j:nat{s <= j && j <= l} -> 
  Tot (q:plain i (j - s) {as_bytes q = Seq.slice (as_bytes p) s j})
  
let slice #i #l p s j = Seq.slice p s j


abstract type plainBuffer (i:id) (l:plainLen) = b:lbuffer l

//usage?

// ghost (was named bufferT; no need to be live)
val as_buffer: #i:id -> #l:plainLen -> pb: plainBuffer i l -> GTot(lbuffer l)
let as_buffer #i #l pb = pb

// for tests
val unsafe_hide_buffer: i:id -> #l:plainLen -> b:lbuffer l -> Tot (plainBuffer i l)
let unsafe_hide_buffer i #l b = b

// usage?
val hide_buffer: i:id -> #l:plainLen -> b:lbuffer l -> GTot (plainBuffer i l)
let hide_buffer i #l b = b

val as_buffer_injective : i:id -> l:plainLen -> p:plainBuffer i l -> Lemma
  (requires True)
  (ensures (hide_buffer i (as_buffer p) == p))
  [SMTPat (as_buffer p)]
let as_buffer_injective i l p = ()


let live #i #l h (p:plainBuffer i l) = Buffer.live h (as_buffer p)
private let live' = live (* live may be shadowed by Buffer.live in case of local open *)

// unconditional access in specs; rename to as_plain? 
val sel_plain: h:mem -> #i:id -> l:UInt32.t -> buf:plainBuffer i (v l){live h buf} -> GTot (plain i (v l))
let sel_plain h #i l buf = sel_bytes h l buf

// restricted 
val bufferRepr: #i:id {~(safeId i)} -> #l:plainLen -> b:plainBuffer i l -> Tot (b':lbuffer l{ b' == as_buffer b})
let bufferRepr #i #l b = b


let create (i:id) (zero:UInt8.t) (len:UInt32.t) :
   StackInline (plainBuffer i (v len))
     (requires (fun h -> is_stack_region h.tip))
     (ensures (fun (h0:mem) p h1 ->
       let p' = p in
       let b = as_buffer p in
       let open FStar.Buffer in
       let live = live' in (* to undo shadowing by FStar.Buffer.live *)
         ~(contains h0 b)
       /\ live h1 p' /\ idx b = 0 /\ length b = v len
       /\ frameOf b = h0.tip
       /\ Map.domain h1.h == Map.domain h0.h
       /\ modifies_0 h0 h1
       /\ as_seq h1 b == Seq.create (v len) zero
       ))
 = Buffer.create zero len

let sub #id #l (b:plainBuffer id l)
               (i:UInt32.t{FStar.Buffer.(v i + idx (as_buffer b)) < pow2 n})
               (len:UInt32.t{FStar.Buffer.(v len <= length (as_buffer b) /\ v i + v len <= length (as_buffer b))}) : Tot (b':plainBuffer id (v len))
  = Buffer.sub b i len
// ...



val load: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> ST (plain i (v l))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 buf /\ sel_plain h1 l buf == r))

let load #i l buf = load_bytes l buf

val store: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> b:plain i (v l) -> ST unit
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf /\ Buffer.modifies_1 (as_buffer #i #(v l) buf) h0 h1 /\
    sel_plain h1 l buf == b
  ))
let store #i l buf b = store_bytes l buf b

