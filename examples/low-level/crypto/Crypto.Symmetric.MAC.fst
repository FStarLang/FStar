(**
  This module multiplexes between different real implementations of polynomial
  MACs. It is oblivious to the static vs one-time allocation of the r part of
  the key (the point where the polynomial is evaluated)
*)
module Crypto.Symmetric.MAC

open Crypto.Symmetric.Bytes
open Flag

module GF = Crypto.Symmetric.GF128
module PS = Crypto.Symmetric.Poly1305.Spec
module PL = Crypto.Symmetric.Poly1305

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let alg i = Flag.mac_of_id i 

(** Field element *)

let elem i = (* dependent; used only ideally *) 
  match alg i with 
  | POLY1305 -> PS.elem
  | GHASH    -> GF.elem

(** Representation of field element as a buffer *)

(* 16-10-26 for the time being, we avoid value-dependent types (after
   erasure and flag inlining) for kremlin. We may later compile those
   two untagged unions. We also use a top-level refinement, so that
   case analysis applies without pattern matching.
   
   See 35380a8a for an older, more type-dependent version *)

let limb = function
  | POLY1305 -> UInt64.t
  | GHASH    -> UInt8.t
let limb_length = function 
  | POLY1305 ->  5 
  | GHASH    -> 16

type buffer' a = b:Buffer.buffer (limb a){Buffer.length b == limb_length a} 
noeq type buffer'' =
  | B_POLY1305 of buffer' POLY1305
  | B_GHASH    of buffer' GHASH
let elemB i = b:buffer''
  { match alg i with 
  | POLY1305 -> is_B_POLY1305 b 
  | GHASH    -> is_B_GHASH b }
let as_buffer (#i:id) (b:elemB i) : GTot(buffer' (alg i)) =
  match b with
  | B_POLY1305 b -> b
  | B_GHASH    b -> b
  
let live h #i (b:elemB i) = Buffer.live h (as_buffer b)

let norm h #i (b:elemB i) =
  match b with
  | B_POLY1305 b -> Crypto.Symmetric.Poly1305.Bigint.norm h b // implies live
  | B_GHASH    b -> Buffer.live h b

(** (partial) words *)
type word = b:Seq.seq u8{Seq.length b <= 16}
type word_16 = lbytes 16

(** Mutable representation of (partial) words as buffers *)
type wordB = b:Buffer.buffer u8{Buffer.length b <= 16}
type wordB_16 = lbuffer 16

let sel_word (h:mem) (b:wordB{Buffer.live h b}) : GTot word =
  Buffer.as_seq h b

val sel_elem: h:mem -> #i:id -> b:elemB i{live h b} -> GTot (elem i)
let sel_elem h #i b =
  match b with
  | B_POLY1305 b -> PL.sel_elem h b
  | B_GHASH    b -> Buffer.as_seq #UInt8.t h b

(** Create and initialize the accumulator *)
val rcreate: rgn:HH.rid{HS.is_eternal_region rgn} -> i:id -> ST (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 ->
    HS.modifies (Set.singleton rgn) h0 h1 /\
    HS.modifies_ref rgn TSet.empty h0 h1))

let rcreate rgn i =
  match alg i with
  | POLY1305 -> B_POLY1305 (FStar.Buffer.rcreate rgn 0UL  5ul)
  | GHASH    -> B_GHASH    (FStar.Buffer.rcreate rgn 0uy 16ul)

// unused for now
val create: i:id -> StackInline (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> Buffer.modifies_0 h0 h1))
let create i =
  match alg i with
  | POLY1305 -> B_POLY1305 (FStar.Buffer.create 0UL  5ul)
  | GHASH    -> B_GHASH    (FStar.Buffer.create 0uy 16ul)

// TODO: generalize length, add functional spec & modifies clause
(** Encode raw bytes of static key as a field element *)
val encode_r: #i:id -> b:elemB i -> raw:lbuffer 16{Buffer.disjoint (as_buffer b) raw} -> Stack unit
  (requires (fun h -> live h b /\ Buffer.live h raw))
  (ensures  (fun h0 _ h1 -> live h1 b))
let encode_r #i b raw =
  match b with 
  | B_POLY1305 b -> PL.clamp raw; PL.toField b raw
  | B_GHASH    b -> Buffer.blit raw 0ul b 0ul 16ul

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
    /\ ~(live h0 b)
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
val poly: #i:id -> cs:Seq.seq (elem i) -> r:elem i -> GTot (elem i)
let poly #i cs r =
  match alg i with 
  | POLY1305 -> PS.poly cs r
  | GHASH    -> admit ()

val mac: #i:id -> cs:Seq.seq (elem i) -> r:elem i -> s:lbytes 16 -> GTot (elem i)
let mac #i cs r s =
  match alg i with
  | POLY1305 -> PS.mac_1305 cs r s
  | GHASH    -> admit ()

(** Create and initialize the accumulator *)
val start: #i:id -> StackInline (elemB i)
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> Buffer.modifies_0 h0 h1))
let start #i = create i

val field_add: #i:id -> elem i -> elem i -> Tot (elem i)
let field_add #i a b =
  match alg i with
  | POLY1305 -> PS.field_add a b
  | GHASH    -> admit ()

val field_mul: #i:id -> elem i -> elem i -> Tot (elem i)
let field_mul #i a b =
  match alg i with
  | POLY1305 -> PS.field_mul a b
  | GHASH    -> admit ()

let op_Plus_At = field_add
let op_Star_At = field_mul

#set-options "--z3timeout 20 --initial_fuel 0 --max_fuel 0"

(** Process one message block and update the accumulator *)
val update: #i:id -> r:elemB i -> a:elemB i -> w:wordB_16 -> Stack unit
  (requires (fun h -> live h r /\ live h a /\ Buffer.live h w
    /\ norm h r /\ norm h a
    /\ Buffer.disjoint_2 (as_buffer r) (as_buffer a) w /\ Buffer.disjoint (as_buffer a) w))
  (ensures  (fun h0 _ h1 ->
    live h0 a /\ live h0 r /\ Buffer.live h0 w /\ live h1 a /\ live h1 r
    /\ norm h1 a
    /\ Buffer.modifies_1 (as_buffer a) h0 h1
    /\ sel_elem h1 a ==
      (sel_elem h0 a +@ encode i (sel_word h0 w)) *@ sel_elem h0 r))

#reset-options "--z3timeout 20"
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
      Crypto.Symmetric.Poly1305.Bigint.eval_eq_lemma h2 h3 a a 5;
      assume false //16-10-26 
    end
  | B_GHASH r, B_GHASH a ->
    begin
      GF.add_and_multiply a w r;
      assume false //16-10-26 
    end

val finish: #i:id -> s:lbuffer 16 -> a:elemB i -> tag:lbuffer 16 -> Stack unit
  (requires (fun h -> Buffer.live h s /\ norm h a /\ Buffer.live h tag /\
    Buffer.disjoint_2 (as_buffer a) s tag /\ Buffer.disjoint s tag ))
  (ensures  (fun h0 _ h1 -> True))
let finish #i s a tag =
  match a with 
  | B_POLY1305 a -> PL.poly1305_finish tag a s; 
                   assume false //16-10-26 strange
  | B_GHASH    a -> GF.gf128_add a s; 
                   Buffer.blit a 0ul tag 0ul 16ul
