module Bug347
#lang-pulse
open Pulse

let limb_t = unit
open FStar.UInt32 { v }
let carry (t: limb_t) = x:UInt32.t { v x <= 1 }
let limb (t: limb_t) = UInt32.t
let uint_v (x: UInt32.t) = v x
let bits (t: limb_t) = 32
let inttype = unit
type secrecy_level = | SEC | PUB
let uint_t (t: inttype) (sec: secrecy_level) = UInt32.t

assume val subborrow: #t:limb_t -> c:carry t -> a:limb t -> b:limb t ->
  Pure (carry t & limb t)
  (requires True)
  (ensures  fun (c', r) ->
    uint_v r - uint_v c' * pow2 (bits t) == uint_v a - uint_v b - uint_v c)

inline_for_extraction
let sub_borrow_st (t:inttype) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:ref (uint_t t SEC) ->
  stt (uint_t t SEC)
  (requires exists* s. pts_to r s ** pure (v cin <= 1))
  (ensures fun c ->
    exists* vr.
    pure (v c <= 1) **
    pts_to r vr **
    pure (v vr - v c * pow2 (bits t) == v x - v y - v cin))

assume val sub_borrow (#t:inttype) : sub_borrow_st t

inline_for_extraction noextract
fn subborrow_st (#t:limb_t) (c_in:carry t) (a:limb t) (b:limb t) (out:ref (limb t))
  requires exists* s. pts_to out s
  returns c_out: carry t
  ensures exists* c0. pts_to out c0 ** pure ((c_out, c0) == subborrow c_in a b)
{
  // The temporary `c_out` is necessary here; simply writing `sub_borrow #t c_in a b out` does not work.
  let c_out = sub_borrow #t c_in a b out;
  c_out
}

[@@expect_failure] // should work
inline_for_extraction noextract
fn subborrow_st2 (#t:limb_t) (c_in:carry t) (a:limb t) (b:limb t) (out:ref (limb t))
  requires exists* s. pts_to out s
  returns c_out: carry t
  ensures exists* c0. pts_to out c0 ** pure ((c_out, c0) == subborrow c_in a b)
{
  sub_borrow #t c_in a b out;
}
