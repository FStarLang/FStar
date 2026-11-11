module JoinLinkFallback
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32

(* The "then" branch leaves the cell at a value known only through a pure fact
   about a fresh existential, mentioning casts and a union discriminator.
   Joining with the (empty) "else" branch generalizes the cell's value; the
   per-branch links recording what the generalized binder stands for are
   proved by SMT and fail here, which used to make every join candidate fail.
   The checker must then fall back to the candidates without links. *)

noeq type st = { code: I32.t }
noeq type status = | Ok : v:st -> status | Other : status

let failed (s:status) : bool = Ok? s && I32.v (Ok?.v s).code < 0

fn peek (_:unit) requires emp returns x: U32.t ensures emp { 3ul }

assume val add (a b: U64.t) (r: ref U32.t) (#v: erased U32.t)
: stt status (pts_to r v) (fun s ->
    exists* v'. pts_to r v' **
      pure (failed s == true \/
            (U64.v (FStar.Int.Cast.uint32_to_uint64 v') == U64.v (U64.add_mod a b) /\
             U64.v a <= U64.v (U64.add_mod a b))))
fn test (r: ref U32.t) (n: U32.t)
  requires pts_to r 0ul
  ensures exists* v . pts_to r v
{
  if (U32.lt 0ul n) {
    let t = peek ();
    r := t;
    let t2 = !r;
    let x = add (FStar.Int.Cast.uint32_to_uint64 t2) (FStar.Int.Cast.uint32_to_uint64 (U32.sub_mod n 1ul)) r;
    ();
  };
  let y = !r;
  ()
}
