module InlineLetPat
#lang-pulse
open Pulse
module U32 = FStar.UInt32
module SZ = FStar.SizeT

(* FStarLang/FStar#4620.  [inline_let] on a destructuring [let].  The pattern
   desugars to [let _letpattern = e; match _letpattern { (r, c) -> ... }], so
   the attribute has to land on [_letpattern]; the normalizer then substitutes
   the pair into the match and iota substitutes its components.  Without it
   each component keeps a binding of its own, which is the right default and
   is what [kept] pins. *)

inline_for_extraction noextract
let divmod (i j : U32.t) : Pure (U32.t & U32.t) (requires U32.v j > 0) (ensures fun _ -> True)
  = (U32.div i j, U32.rem i j)

fn inlined (t x : U32.t)
  requires pure (U32.v t > 0)
  returns  _:U32.t
{
  let [@@@inline_let] (row, col) = divmod x t;
  U32.add_mod (U32.mul_mod row t) (U32.add_mod col (U32.mul_mod row col))
}

fn kept (t x : U32.t)
  requires pure (U32.v t > 0)
  returns  _:U32.t
{
  let (krow, kcol) = divmod x t;
  U32.add_mod (U32.mul_mod krow t) (U32.add_mod kcol (U32.mul_mod krow kcol))
}

(* The same, written in F*. *)
let f_inlined (t x : U32.t) : Pure U32.t (requires U32.v t > 0) (ensures fun _ -> True) =
  [@@inline_let] let (frow, fcol) = divmod x t in
  U32.add_mod (U32.mul_mod frow t) (U32.add_mod fcol (U32.mul_mod frow fcol))

fn main () returns r:SZ.t
{
  let a = inlined 3ul 10ul;
  let b = kept 3ul 10ul;
  let c = f_inlined 3ul 10ul;
  if (a = 13ul && b = 13ul && c = 13ul) { 0sz } else { 1sz }
}
