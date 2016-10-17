module Crypto.Symmetric.MAC

open Crypto.Symmetric.Bytes
open Flag

module GF = Crypto.Symmetric.GF128
module PLS = Crypto.Symmetric.Poly1305.Spec
module PL = Crypto.Symmetric.Poly1305

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type elem128 = lbytes 16

let alg i = Flag.mac_of_id i 

(* this file multiplexes between different real implementations of
   polynomial MACs. It is indifferent to the static vs one-time 
   allocation of the r part of the key *)

let elem i = 
  match alg i with
  | POLY1305 -> PLS.elem
  | GHASH    -> elem128

let elemB i = 
  b: Buffer.buffer 
    (if alg i = POLY1305 then UInt64.t else UInt8.t) 
    {Buffer.length b = (if alg i = POLY1305 then 5 else 16)}
//  match alg i with
//  | POLY1305 -> PL.elemB
//  | GHASH    -> lbuffer 16

let live h #i (b:elemB i) = 
  match alg i with
  | POLY1305 -> Buffer.live #UInt64.t h b /\ 
               //16-10-17 annoying; implying live.
               Crypto.Symmetric.Poly1305.Bigint.norm h b
  | GHASH    -> Buffer.live #UInt8.t h b

let rcreate (rgn:HH.rid{HS.is_eternal_region rgn}) i: ST (elemB i)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    HS.modifies (Set.singleton rgn) h0 h1 /\
    HS.modifies_ref rgn TSet.empty h0 h1 
  )) =   
  match alg i with 
  | POLY1305 -> FStar.Buffer.rcreate rgn 0UL 5ul
  | GHASH    -> FStar.Buffer.rcreate rgn 0uy 16ul

let create i : StackInline (elemB i) 
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 ->
    Buffer.modifies_0 h0 h1
  )) = 
  match alg i with 
  | POLY1305 -> FStar.Buffer.create 0UL 5ul
  | GHASH    -> FStar.Buffer.create 0uy 16ul

(* avoiding:
let frameOf #i (b:elemB i) = 
  match alg i with
  | POLY1305 -> Buffer.frameOf #UInt64.t b
  | GHASH    -> Buffer.frameOf #UInt8.t b
*)

let sel_elem h #i (b:elemB i{live h b}) : elem i =
  match alg i with 
  | POLY1305 -> PL.sel_elem h b
  | GHASH    -> Buffer.as_seq #UInt8.t h b 


let encode_r i (b:elemB i) (raw:lbuffer 16) = 
  match alg i with 
  | POLY1305 -> PL.clamp raw; 
               PL.toField b raw
  | GHASH    -> Buffer.blit raw 0ul b 0ul 16ul

let encode h i (w:lbytes 16): elem i = 
  match alg i with 
  | POLY1305 -> PLS.encode w
  | GHASH    -> w 

(*
let mac i (log:Seq.seq (elem i)) (r:elem i) (s:lbytes 16) : Tot (lbytes 16) = 
  match alg i with
  | POLY1305 -> PLS.mac_1305 log r s 
  | GHASH    -> admit()
*)

private let encodeB i w : elemB i = 
  match alg i with 
  | POLY1305 -> let b = Buffer.create 0UL 5ul in 
               PL.toField_plus_2_128 b w;
               b
  | GHASH    -> w 

assume val gf128_poly: cs:Seq.seq elem128 -> r:elem128 -> Tot elem128

(* we also need an abstract polynomial-evaluation spec *)
//16-10-17  removing abstraction for now
let poly #i (cs:Seq.seq (elem i)) (r:elem i) : elem i = 
  match alg i with 
  | POLY1305 -> PLS.poly cs r 
  | GHASH    -> gf128_poly cs r

let start i = create i 
  
let update #i (r: elemB i) (a:elemB i) (w:lbuffer 16) = 
  push_frame();
  let e = encodeB i w in 
  match alg i with 
  | POLY1305 -> PL.add_and_multiply a e r (* to be adapted from poly1305.mac *)
  | GHASH    -> GF.add_and_multiply a w r;
  pop_frame()
  (* TODO: re-use the elem buffer 
     rather that create a fresh one, maybe in the accumulator *)

let finish i (s:lbuffer 16) (a:elemB i) (tag:lbuffer 16) = 
  match alg i with 
  | POLY1305 -> PL.poly1305_finish tag a s
  | GHASH    -> GF.gf128_add a s; 
               Buffer.blit a 0ul tag 0ul 16ul

      

  


  








