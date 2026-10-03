(* Section 99.  A read whose value nothing wants used to survive as a
   statement -- [(void)(a[0]);] -- because Simplify asked [is_pure], which
   answers "may this be moved" and is too strong: a read may not move across
   a write, and may always be deleted.

   [comb] ignores its first argument, so [v0] is dead only *after* inlining,
   which is why the source looks like it uses both.  [kept] is the other half:
   a discarded *call* is not droppable and must stay exactly where it is. *)
module DeadRead
#lang-pulse
open Pulse
module A   = Pulse.Lib.Array
module SZ  = FStar.SizeT
module U32 = FStar.UInt32
module I32 = FStar.Int32

inline_for_extraction
let comb (x y: U32.t) : U32.t = y

fn dead_load (a: A.array U32.t)
  requires A.pts_to a #1.0R 's ** pure (Seq.length 's == 4)
  ensures exists* w. A.pts_to a #1.0R w
{
  A.pts_to_len a;
  let v0 = a.(0sz);
  let v1 = a.(1sz);
  a.(0sz) <- comb v0 v1;
}

fn bump (r: ref U32.t)
  requires pts_to r 'n
  ensures pts_to r (U32.add_mod 'n 1ul)
{
  r := U32.add_mod !r 1ul;
}

(* The discarded term is a call, which has an effect the program depends on. *)
fn kept (a: A.array U32.t) (r: ref U32.t)
  requires A.pts_to a #1.0R 's ** pts_to r 'n ** pure (Seq.length 's == 4)
  ensures exists* w m. A.pts_to a #1.0R w ** pts_to r m
{
  A.pts_to_len a;
  bump r;
  let v0 = a.(2sz);
  let v1 = a.(3sz);
  a.(2sz) <- comb v0 v1;
}

fn main () requires emp returns c: I32.t ensures emp
{
  let a = A.alloc 0ul 4sz;
  A.pts_to_len a;
  a.(1sz) <- 7ul;
  a.(3sz) <- 9ul;
  dead_load a;
  A.pts_to_len a;
  let mut r = 0ul;
  kept a r;
  A.pts_to_len a;
  let x = a.(0sz);
  let y = a.(2sz);
  let n = !r;
  A.free a;
  if (U32.eq x 7ul && U32.eq y 9ul && U32.eq n 1ul) { 0l } else { 1l }
}
