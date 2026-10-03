module PulsePartial

#lang-pulse

open Pulse.Lib.Pervasives
module U = FStar.UInt32

type kind = | A | B

fn callee (a:kind) (b c:U.t)
  requires emp
  returns result:U.t
  ensures emp
{
  if A? a {
    U.add_mod b c
  } else {
    0ul
  }
}

fn forward (a:kind) (b c:U.t)
  requires emp
  returns result:U.t
  ensures emp
{
  callee a b c
}

fn wrapper (b c:U.t)
  requires emp
  returns result:U.t
  ensures emp
{
  callee A b c
}

(* Section 103.  The same shape at the two other ways of building a value:
   a constructor with an argument, and a record.  A nullary constructor is
   free in every target, which makes it the easy case to argue; these are the
   ones the rule has to be right about. *)
noeq type cfg = { c_k : kind; c_n : U.t }

fn takes_cfg (cf: cfg) (b c: U.t)
  requires emp
  returns result:U.t
  ensures emp
{
  if A? cf.c_k {
    U.add_mod (U.add_mod b c) cf.c_n
  } else {
    cf.c_n
  }
}

fn wrap_record (b c:U.t)
  requires emp
  returns result:U.t
  ensures emp
{
  takes_cfg { c_k = A; c_n = 10ul } b c
}

fn main ()
  returns x: FStar.Int32.t
{
  let r = wrapper 3ul 4ul;
  let s = forward B 3ul 4ul;
  let t = wrap_record 3ul 4ul;
  if (U.eq r 7ul && U.eq s 0ul && U.eq t 17ul) { 0l } else { 1l }
}
