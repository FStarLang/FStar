module BU = FStarC_Compiler_Util
module Z = FStarC_BigInt

type hash_code = int

let cmp_hash (x:hash_code) (y:hash_code) : Z.t = Z.of_int (x-y)

let to_int (i:int) = Z.of_int i

let of_int (i:Z.t) = Z.to_int i
let of_string (s:string) = BatHashtbl.hash s

(* This function is taken from Bob Jenkins'
   http://burtleburtle.net/bob/hash/doobs.html
   
   It's defined there as a mix on 32 bit integers.
   
   I'm abusing it here by using it on OCaml's 63 bit
   integers.

   But it seems to work well, at least in comparison
   to some simpler mixes that I tried. E.g., using
   this mix taken from Lean (src/runtime/hash.h)

uint64 hash(uint64 h1, uint64 h2) {
    h2 -= h1; h2 ^= (h1 << 16);
    h1 -= h2; h2 ^= (h1 << 32);
    h2 -= h1; h2 ^= (h1 << 20);
    return h2;
}

   But, it produces many collisions, see, e.g., in
   tests/FStar.Tests.Pars.test_hashes
*)   
let mix (a: hash_code) (b:hash_code) =
  let c = 11 in
  (* a -= b; a -= c; a ^= (c >> 13); *)
  let a = a - b in
  let a = a - c in
  (* skip this step since c lsr 13 = 0 *)
  (* let a = a lxor (c lsr 13) in *)
  (* b -= c; b -= a; b ^= (a << 8); *)
  let b = b - c in
  let b = b - a in
  let b = b lxor (a lsl 8) in
  (* c -= a; c -= b; c ^= (b >> 13); *)
  let c = c - a in
  let c = c - b in
  let c = c lxor (b lsr 13) in
  (*  a -= b; a -= c; a ^= (c >> 12); *)  
  let a = a - b in
  let a = a - c in
  let a = a lxor (c lsr 12) in
  (*  b -= c; b -= a; b ^= (a << 16); *)
  let b = b - c in
  let b = b - a in
  let b = b lxor (a lsl 16) in
  (*  c -= a; c -= b; c ^= (b >> 5); *)
  let c = c - a in
  let c = c - b in
  let c = c lxor (b lsr 5) in
  (* a -= b; a -= c; a ^= (c >> 3); *)
  let a = a - b in
  let a = a - c in
  let a = a lxor (c lsr 3) in
  (* b -= c; b -= a; b ^= (a << 10); *)
  let b = b - c in
  let b = b - a in
  let b = b lxor (a lsl 10) in
  (* c -= a; c -= b; c ^= (b >> 15); *)
  let c = c - a in
  let c = c - b in
  let c = c lxor (b lsr 15) in
  c

let string_of_hash_code h = string_of_int h
