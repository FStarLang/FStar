module Experiment.Parsing

open FStar.Seq
open FStar.UInt8
open FStar.UInt32
open FStar.Ghost
open FStar.Int.Cast
open FStar.ImmBuffer

assume Mod_1: forall i. i % (sizeof byte) = 0

type validator = 
  b:buffer u8 -> len:UInt32.t -> Pure (result UInt32.t)
    (requires (b2t(v len <= length (b))))
    (ensures  (fun l -> Correct? l ==> v (correct l) <= length (b)))

type valid (b:buffer u8) (l:UInt32.t) (v:validator) = 
  UInt32.v l <= length b /\ Correct? (v b l)

type lsize = n:int{n = 1 \/ n = 2 \/ n = 3}
type csize = n:t{v n = 1 \/ v n = 2 \/ v n = 3}

val read_length: 
  b:buffer u8 -> 
  n:csize{v n <= length b} -> 
  Tot UInt32.t
let read_length b n =
  if n = 1ul then (
    let b0 = read b 0ul in
    uint8_to_uint32 b0
  ) else if n = 2ul then (
    let b1 = read b 0ul in
    let b0 = read b 1ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    b0 |^ (b1 <<^ 8ul)
  ) else (
    let b2 = read b 0ul in
    let b1 = read b 1ul in
    let b0 = read b 2ul in
    let b0 = uint8_to_uint32 b0 in
    let b1 = uint8_to_uint32 b1 in
    let b2 = uint8_to_uint32 b2 in
    b0 |^ (b1 <<^ 8ul) |^ (b2 <<^ 16ul)
  )

val vlparse: n:csize -> b:buffer u8 -> len:UInt32.t -> Pure (result UInt32.t)
  (requires (b2t(v len <= length b)))
  (ensures  (fun l -> Correct? l ==> v (correct l) <= length (b)))
let vlparse n b len =
  if n >^ len then Error "Too short"
  else 
    let l = read_length b n in
    if length b < v n + v l then Error "Wrong vlbytes format"
    else (
      let b' = sub b 0ul (n +^ l) in
      Correct (n +^ l)
    )

noeq type vbuffer ($v:validator)= b:buffer u8{valid b b.length v}

type vlbytes (n:lsize) = vbuffer (vlparse (uint_to_t n))

(* val vlbuffer_parse: n:csize -> validator *)
(* let vlbuffer_parse n = fun b len -> *)
  

(* type vlbytes (n:lsize) = b:buffer u8{ *)
(*   length b >= n /\ (let len_bytes = uint_to_t n in *)
(*     valid b (read_length b len_bytes) (vlparse len_bytes)) } *)

