module FStar.SizeT
open FStar.Ghost
module I64 = FStar.Int64

(* This is only intended as a model, but will be extracted natively by Krml
   with the correct C semantics *)

(* We assume the existence of some lower bound on the size, 
   where the bound is at least 2^16 *)
assume
val bound : x:erased nat { x >= pow2 16 }

let t = x:U64.t { U64.v x < bound }

let fits x =
  FStar.UInt.fits x U64.n == true /\
  x < bound

let fits_at_least_16 _ = ()

let v x =
  U64.v x

let uint_to_t x =
  U64.uint_to_t x

let size_v_inj (x: t) = ()
let size_uint_to_t_inj (x: nat) = ()


/// These two predicates are only used for modeling purposes, and their definitions must
/// remain abstract to ensure they can only be introduced through a static assert.
/// We simply define them as True here
let fits_u32 = (reveal bound >= pow2 32) == true
let fits_u64 = (reveal bound == pow2 64)

let fits_u64_implies_fits_32 ()
  : Lemma
    (requires fits_u64)
    (ensures fits_u32)
  = ()

let fits_u32_implies_fits (x:nat)
  : Lemma
    (requires fits_u32 /\ x < pow2 32)
    (ensures fits x)
  = ()

let fits_u64_implies_fits (x:nat)
  : Lemma
    (requires fits_u64 /\ x < pow2 64)
    (ensures fits x)
  = ()

let of_u32 (x: U32.t)
  = uint_to_t (U32.v x)

let of_u64 (x: U64.t)
  = uint_to_t (U64.v x)

let uint16_to_sizet x = uint_to_t (U16.v x)
let uint32_to_sizet x = uint_to_t (U32.v x)
let uint64_to_sizet x = uint_to_t (U64.v x)

let fits_lte x y = ()

let add x y = U64.add x y
let sub x y = U64.sub x y
let mul x y = U64.mul x y
let div x y = 
  let res = U64.div x y in
  fits_lte (U64.v res) (U64.v x);
  FStar.Math.Lib.slash_decr_axiom (U64.v x) (U64.v y);
  assert (U64.v x / U64.v y <= U64.v x);
  res
let rem x y = U64.rem x y
let gt x y = U64.gt x y
let gte x y = U64.gte x y
let lt x y = U64.lt x y
let lte x y = U64.lte x y
