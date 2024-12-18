module FStar.SizeT
open FStar.Ghost
module I64 = FStar.Int64

(* This is only intended as a model, but will be extracted natively by Krml
   with the correct C semantics *)

(* We assume the existence of some lower bound on the size,
   where the bound is at least 2^16 *)
assume
val bound : x:erased nat { x >= pow2 16 }

type t : eqtype = | Sz : (x:U64.t { U64.v x < bound }) -> t

let fits x =
  FStar.UInt.fits x U64.n == true /\
  x < bound

let fits_at_least_16 _ = ()

let v x =
  U64.v (Sz?.x x)

irreducible
let uint_to_t x =
  Sz (U64.uint_to_t x)

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
let sizet_to_uint32 x = FStar.Int.Cast.uint64_to_uint32 (Sz?.x x)
let sizet_to_uint64 x = (Sz?.x x)

let fits_lte x y = ()

let add x y = Sz <| U64.add x.x y.x
let sub x y = Sz <| U64.sub x.x y.x
let mul x y = Sz <| U64.mul x.x y.x

let div x y =
  let res_n = U64.div x.x y.x in
  FStar.Math.Lib.slash_decr_axiom (U64.v x.x) (U64.v y.x);
  assert (U64.v res_n < bound);
  let res = Sz res_n in
  fits_lte (U64.v res.x) (U64.v x.x);
  res

let rem x y = Sz <| U64.rem x.x y.x
let gt  x y = U64.gt  x.x y.x
let gte x y = U64.gte x.x y.x
let lt  x y = U64.lt  x.x y.x
let lte x y = U64.lte x.x y.x
