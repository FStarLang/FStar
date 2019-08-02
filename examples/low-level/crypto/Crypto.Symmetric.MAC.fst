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
(**
  This module multiplexes between different real implementations of polynomial
  MACs. It is oblivious to the static vs one-time allocation of the r part of
  the key (the point where the polynomial is evaluated).

  It has functions to allocate keys and compute MACs incrementally on
  stack-based accumulators (start; update; finish), as a refinement of 
  their ghost polynomial specification.
*)
module Crypto.Symmetric.MAC

open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Flag
open FStar.HyperStack.ST

module GS = Crypto.Symmetric.GF128.Spec
module GF = Crypto.Symmetric.GF128
module PS = Crypto.Symmetric.Poly1305.Spec
module PL = Crypto.Symmetric.Poly1305

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

type id = id * UInt128.t //NS: why not this definition : i:id & iv (alg i)
let alg (i:id) = macAlg_of_id (fst i) 

type text = Seq.seq (lbytes 16) // Used to be seq elem, then seq (lbytes 16)

val text_to_PS_text: t:text -> Tot (t':PS.text{
  Seq.length t == Seq.length t' /\
  (forall (i:nat).{:pattern Seq.index t' i}
    i < Seq.length t ==> Seq.index t i == Seq.index t' i)})
  (decreases (Seq.length t))
let rec text_to_PS_text t =
  if Seq.length t = 0 then Seq.empty
  else
    Seq.cons (Seq.head t)
                       (text_to_PS_text (Seq.tail t))

(** Field element *)
let elem i = (* dependent; used only ideally *)
  match alg i with 
  | POLY1305 -> PS.elem
  | GHASH    -> GS.elem

let zero i : elem i = 
  match alg i with 
  | POLY1305 -> PS.zero
  | GHASH    -> GS.zero

(** Private representation of a field element as a buffer *)

(* 16-10-26 for the time being, we avoid value-dependent types (after
   erasure and flag inlining) for Kremlin. We may later compile those
   to untagged unions. We also use a top-level refinement, so that
   case analysis applies without pattern matching.
   
   See 35380a8a for an older, more type-dependent version *)

unfold inline_for_extraction 
let limb = function
  | POLY1305 -> UInt64.t
  | GHASH    -> UInt8.t

unfold inline_for_extraction
let limb_length = function
  | POLY1305 ->  5
  | GHASH    -> 16

inline_for_extraction unfold
type buffer_of a = b:Buffer.buffer (limb a){Buffer.length b == limb_length a}

// TODO: workaround for #759
inline_for_extraction type _buffer_of a = buffer_of a

// private?
noeq type _buffer =
  | B_POLY1305 of buffer_of POLY1305
  | B_GHASH    of buffer_of GHASH

type pub_elemB (i:id) = b:_buffer
  { match alg i with
  | POLY1305 -> B_POLY1305? b
  | GHASH    -> B_GHASH? b }

abstract type elemB (i:id) = pub_elemB i

noextract val reveal_elemB : #i:id -> elemB i -> GTot (pub_elemB i)
let reveal_elemB #i e = e

val as_buffer: #i:id -> elemB i -> GTot (_buffer_of (alg i))
let as_buffer #i = function
  | B_POLY1305 b -> b
  | B_GHASH    b -> b

val live: mem -> #i:id -> elemB i -> Type0
let live h #i b = Buffer.live h (as_buffer b)

val norm: mem -> #i:id -> b:elemB i -> Type0
let norm h #i b = 
  match reveal_elemB b with
  | B_POLY1305 b -> Crypto.Symmetric.Poly1305.Bigint.norm h b // implies live
  | B_GHASH    b -> Buffer.live h b


(** message words (not necessarily a full word. *)
let wlen = 16ul

type word = b:Seq.seq u8{Seq.length b <= UInt32.v wlen}

type word_16 = lbytes (UInt32.v wlen)

(** Mutable representation of (partial) words as buffers *)
type wordB = b:Buffer.buffer u8{Buffer.length b <= UInt32.v wlen}

type wordB_16 = lbuffer (UInt32.v wlen)

val sel_word: h:mem -> b:wordB{Buffer.live h b} -> GTot word
let sel_word h b = Buffer.as_seq h b

val sel_elem: h:mem -> #i:id -> b:elemB i{live h b} -> GTot (elem i)
let sel_elem h #i b = 
  match reveal_elemB b with
  | B_POLY1305 b -> PL.sel_elem h b
  | B_GHASH    b -> Buffer.as_seq h b

val frame_norm: h0:mem -> h1:mem -> #i:id -> b:elemB i{live h1 b} -> Lemma
  (requires (norm h0 b /\
    Buffer.as_seq h0 (as_buffer b) == Buffer.as_seq h1 (as_buffer b)))
  (ensures  (norm h1 b))
let frame_norm h0 h1 #i b =
  match alg i with
  | POLY1305 ->
    Crypto.Symmetric.Poly1305.Bigint.norm_eq_lemma h0 h1 (as_buffer b) (as_buffer b)
  | _ -> ()

val eq_sel_elem: h:mem -> #i:id -> b1:elemB i{live h b1} -> b2:elemB i{live h b2} -> Lemma
 (requires (Buffer.as_seq h (as_buffer b1) == Buffer.as_seq h (as_buffer b2)))
 (ensures  (sel_elem h b1 == sel_elem h b2))
let eq_sel_elem h #i b1 b2 =
  match alg i with
  | POLY1305 ->
    Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h h
      (as_buffer b1) (as_buffer b2) (limb_length POLY1305)
  | _ -> ()

val frame_sel_elem: h1:mem -> h2:mem -> #i:id -> b:elemB i{live h1 b /\ live h2 b} -> Lemma
 (requires (Buffer.as_seq h1 (as_buffer b) == Buffer.as_seq h2 (as_buffer b)))
 (ensures  (sel_elem h1 b == sel_elem h2 b))
let frame_sel_elem h1 h2 #i b =
  match alg i with
  | POLY1305 ->
    Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h1 h2
      (as_buffer b) (as_buffer b) (limb_length POLY1305)
  | _ -> ()

(** Create and initialize an element (used for r) *)
val rcreate: rgn:HH.rid{HS.is_eternal_region rgn} -> i:id -> ST (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 ->
    HS.modifies (Set.singleton rgn) h0 h1 /\
    HS.modifies_ref rgn Set.empty h0 h1 /\
    ~(HS.is_mm ((Buffer.content (as_buffer r)))) /\
    Buffer.frameOf (as_buffer r) == rgn /\
    ~(live h0 r) /\live h1 r))
let rcreate rgn i =
  match alg i with
  | POLY1305 -> B_POLY1305 (FStar.Buffer.rcreate rgn 0UL  5ul)
  | GHASH    -> B_GHASH    (FStar.Buffer.rcreate rgn 0uy wlen)

val create: i:id -> StackInline (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> 
     let b = as_buffer r in 
     ~(Buffer.contains h0 b) /\ 
     norm h1 r /\
     sel_elem h1 r = zero i /\
     Buffer.frameOf b = HS.(h0.tip) /\ // /\ Map.domain h1.h == Map.domain h0.h
     Buffer.modifies_0 h0 h1 ))

let create i =
  match alg i with
  | POLY1305 -> 
      // hide in Poly1305.fst?
      let b = FStar.Buffer.create 0uL 5ul in
      let h1 = ST.get() in 
      Crypto.Symmetric.Poly1305.Bigint.eval_null h1 b 5;
      //assert(Crypto.Symmetric.Poly1305.Bigint.norm h1 b);
      B_POLY1305 b
  | GHASH -> 
      B_GHASH (FStar.Buffer.create 0uy 16ul)

// TODO: generalize length, add functional spec
(** Encode raw bytes of static key as a field element *)
val encode_r: #i:id -> b:elemB i -> raw:lbuffer 16{Buffer.disjoint (as_buffer b) raw} -> Stack unit
  (requires (fun h -> live h b /\ Buffer.live h raw))
  (ensures  (fun h0 _ h1 -> 
    norm h1 b /\ 
    Buffer.live h1 raw /\ 
    (match alg i with 
      | POLY1305 -> Buffer.modifies_2 (as_buffer b) raw h0 h1
      | GHASH -> Buffer.modifies_1 (as_buffer b) h0 h1)))
let encode_r #i b raw =
  match b with 
  | B_POLY1305 b -> 
      PL.clamp raw; 
      PL.toField b raw
  | B_GHASH    b -> 
      //let h0 = ST.get () in
      //assert (Buffer.modifies_1 raw h0 h0); // Necessary for triggering right lemmas
      Buffer.blit raw 0ul b 0ul 16ul

// TODO: generalize to word
(** Encode a word of a message as a field element *)
val encode: i:id -> w:word_16 -> GTot (elem i)
let encode i w =
  match alg i with 
  | POLY1305 -> PS.encode w
  | GHASH    -> w //PS.pad_0 w (16 - Seq.length w)

(** Encode a word of a message as a field element in a buffer *)
private val encodeB: i:id -> w:wordB_16 -> StackInline (elemB i)
  (requires (fun h -> Buffer.live h w))
  (ensures  (fun h0 b h1 -> Buffer.live h1 w /\ live h1 b /\ norm h1 b
    /\ Buffer.modifies_0 h0 h1
    /\ ~(Buffer.contains h0 (as_buffer b))
    /\ sel_elem h1 b == encode i (sel_word h1 w)))
let encodeB i w =
  match alg i with 
  | POLY1305 ->
      let b = Buffer.create 0UL 5ul in
      PL.toField_plus_2_128 b w;
      B_POLY1305 b
  | GHASH ->
      let b = Buffer.create 0uy 16ul in
      let h0 = ST.get () in
      Buffer.blit w 0ul b 0ul 16ul;
      let h1 = ST.get () in
      Seq.lemma_eq_intro (sel_word h0 w) (Seq.slice (Buffer.as_seq h0 w) 0 16);
      Seq.lemma_eq_intro (Buffer.as_seq h1 b) (Seq.slice (Buffer.as_seq h1 b) 0 16);
      B_GHASH b

(** Polynomial evaluation *)
val poly: #i:id -> cs:text -> r:elem i -> Tot (elem i)
let poly #i cs r =
  match alg i with 
  | POLY1305 -> PS.poly (text_to_PS_text cs) r
  | GHASH    -> GS.poly cs r


(** Create and initialize the accumulator *)
val start: #i:id -> StackInline (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> 
     let b = as_buffer r in 
       ~(Buffer.contains h0 b)
     /\ norm h1 r 
     /\ sel_elem h1 r = zero i 
     /\ Buffer.frameOf b = HS.(h0.tip) // /\ Map.domain h1.h == Map.domain h0.h
     /\ Buffer.modifies_0 h0 h1 ))
//16-11-27 factor out this kind of post?

let start #i = create i

val field_add: #i:id -> elem i -> elem i -> Tot (elem i)
let field_add #i a b =
  match alg i with
  | POLY1305 -> PS.field_add a b
  | GHASH    -> GS.op_Plus_At a b

val field_mul: #i:id -> elem i -> elem i -> Tot (elem i)
let field_mul #i a b =
  match alg i with
  | POLY1305 -> PS.field_mul a b
  | GHASH    -> GS.op_Star_At a b

let op_Plus_At #i e1 e2 = field_add #i e1 e2
let op_Star_At #i e1 e2 = field_mul #i e1 e2

val poly_empty: #i:id -> t:text{Seq.length t == 0} -> r:elem i ->
  Lemma (poly #i t r == zero i)
let poly_empty #i t r =
  match alg i with
  | POLY1305 -> PL.poly_empty (text_to_PS_text t) r
  | GHASH    -> GS.poly_empty t r

val poly_cons: #i:id -> x:word_16 -> xs:text -> r:elem i ->
  Lemma (poly #i (Seq.cons x xs) r == (poly #i xs r +@ encode i x) *@ r)
let poly_cons #i x xs r =
  match alg i with
  | POLY1305 ->
    assert (Seq.equal (text_to_PS_text (Seq.cons x xs))
                      (Seq.cons x (text_to_PS_text xs)));
    PL.poly_cons x (text_to_PS_text xs) r
  | GHASH    ->  GS.poly_cons x xs r; GS.add_comm (poly #i xs r) (encode i x)

#set-options "--z3rlimit 20 --initial_fuel 0 --max_fuel 0"

(** Process one message block and update the accumulator *)
val update: #i:id -> r:elemB i -> a:elemB i -> w:wordB_16 -> Stack unit
  (requires (fun h -> live h r /\ live h a /\ Buffer.live h w
    /\ norm h r /\ norm h a
    /\ Buffer.disjoint_2 (as_buffer r) (as_buffer a) w 
    /\ Buffer.disjoint (as_buffer a) w))
  (ensures  (fun h0 _ h1 ->
    live h0 a /\ live h0 r /\ Buffer.live h0 w /\ live h1 a ///\ live h1 r
    /\ norm h1 a
    /\ Buffer.modifies_1 (as_buffer a) h0 h1
    /\ sel_elem h1 a == (sel_elem h0 a +@ encode i (sel_word h0 w)) *@ sel_elem h0 r))

#set-options "--z3rlimit 40"

// TODO: use encodeB?
let update #i r a w =
  let h0 = ST.get () in
  match r, a with
  | B_POLY1305 r, B_POLY1305 a ->
    begin
      push_frame();
      let e = Buffer.create 0UL 5ul in
      PL.toField_plus_2_128 e w;
      let h1 = ST.get () in
      Crypto.Symmetric.Poly1305.Bigint.norm_eq_lemma h0 h1 a a;
      Crypto.Symmetric.Poly1305.Bigint.norm_eq_lemma h0 h1 r r;
      assert (PL.sel_elem h1 e == encode i (sel_word h0 w));
      PL.add_and_multiply a e r;
      let h2 = ST.get () in
      //assert (PL.sel_elem h2 a == (PL.sel_elem h1 a +@ PL.sel_elem h1 e) *@ PL.sel_elem h1 r);
      Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h0 h1 r r 5;
      Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h0 h1 a a 5;
      pop_frame();

      let h3 = ST.get () in
      Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h2 h3 a a 5
    end
  | B_GHASH r, B_GHASH a -> GF.add_and_multiply a w r


let taglen = 16ul
type tag = lbytes (UInt32.v taglen) 
type tagB = lbuffer (UInt32.v taglen)

(** Complete MAC-computation specifications *)
val mac: #i:id -> cs:text -> r:elem i -> s:tag -> GTot tag
let mac #i cs r s =
  match alg i with
  | POLY1305 -> PS.mac_1305 (text_to_PS_text cs) r s
  | GHASH    -> GS.mac cs r s


val finish: #i:id -> s:tagB -> a:elemB i -> t:tagB -> Stack unit
  (requires (fun h -> 
    Buffer.live h s /\ 
    norm h a /\ 
    Buffer.live h t /\
    Buffer.disjoint_2 (as_buffer a) s t /\ Buffer.disjoint s t))
  (ensures  (fun h0 _ h1 -> live h0 a /\ Buffer.live h0 s
    /\ live h1 a
    /\ Buffer.live h1 s
    /\ Buffer.live h1 t
    /\ Buffer.modifies_2 (as_buffer a) t h0 h1
    /\ (
    let tv = Buffer.as_seq h1 t in
    let sv = Buffer.as_seq h0 s in
    let av = sel_elem h0 a in
    match alg i with
    | POLY1305 -> Seq.equal tv (PS.finish av sv)
    | GHASH    -> Seq.equal tv (GS.finish av sv) )))

let finish #i s a t =
  match a with
  | B_POLY1305 a -> PL.poly1305_finish t a s
  | B_GHASH    a ->
    begin
    GF.finish a s;
    Buffer.blit a 0ul t 0ul 16ul;
    let h1 = ST.get() in
    Seq.lemma_eq_intro (Buffer.as_seq h1 t) (Seq.slice (Buffer.as_seq h1 t) 0 16)
    end
