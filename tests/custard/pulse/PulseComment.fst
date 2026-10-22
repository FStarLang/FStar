(* Section 120.  [Pulse.Lib.Comment] in the shapes pulse/test's CommentTest
   does not reach: a comment inside a loop body, one around a call result,
   one nested inside another, and one whose value nothing reads.

   The last is the interesting one.  A comment is an operation with an
   operand, and every rule in the IR that deletes an operation asks whether
   its operand can be dropped; the answer here has to be no, or the text the
   author wrote goes with the value. *)
module PulseComment
#lang-pulse
open Pulse
open Pulse.Lib.Comment
module SZ  = FStar.SizeT
module U32 = FStar.UInt32
module I32 = FStar.Int32
module A = Pulse.Lib.Array

fn discarded_load (a: A.array U32.t)
  requires A.pts_to a #1.0R 's ** pure (Seq.length 's == 1)
  ensures A.pts_to a #1.0R 's
{
  A.pts_to_len a;
  let first = a.(0sz);
  let middle = U32.add_mod first 1ul;
  let unused = comment_gen "discarded load" (U32.add_mod middle 2ul) "load done";
}

fn bump (r: ref U32.t)
  requires pts_to r 'n
  returns v: U32.t
  ensures pts_to r (U32.add_mod 'n 1ul) ** pure (v == U32.add_mod 'n 1ul)
{
  let v = U32.add_mod !r 1ul;
  r := v;
  v
}

inline_for_extraction
fn loaded_value (a: A.array U32.t) (r: ref U32.t)
  requires A.pts_to a #1.0R 's ** pts_to r 'n ** pure (Seq.length 's == 1)
  returns v: U32.t
  ensures A.pts_to a #1.0R 's ** pts_to r (U32.add_mod 'n 1ul)
{
  let n = bump r;
  A.pts_to_len a;
  let first = a.(0sz);
  let middle = U32.add_mod first n;
  U32.add_mod middle 2ul
}

fn twice (x: U32.t)
  returns y: U32.t
{
  comment "doubling";
  U32.add_mod x x
}

fn count_to (n: SZ.t)
  returns t: U32.t
{
  comment "the running total";
  let mut acc = 0ul;
  let mut i = 0sz;
  while (let vi = !i; SZ.(vi <^ n))
  invariant exists* (vi:SZ.t) (t:U32.t). (
    i |-> vi ** acc |-> t ** pure (SZ.v vi <= SZ.v n)
  )
  decreases (SZ.v n - SZ.v (!i))
  {
    comment "one step";
    let vi = !i;
    let t = !acc;
    acc := comment_gen "accumulate" (U32.add_mod t 1ul) "accumulated";
    i := SZ.(vi +^ 1sz);
  };
  !acc
}

fn main () returns c: I32.t
{
  let a = A.alloc 7ul 1sz;
  discarded_load a;
  let mut r = 0ul;
  let unused_load = loaded_value a r;
  A.free a;
  let unused_effect = comment_gen "discarded effect" (bump r) "effect done";
  let n = !r;
  (* A comment around a call result, and one nested inside another. *)
  let t = comment_gen "outer before"
            (comment_gen "inner before" (count_to 4sz) "inner after")
            "outer after";
  (* Nothing reads this one.  The comment survives anyway. *)
  let unused = comment_gen "kept" 0ul "even unread";
  let d = twice t;
  if (U32.eq n 2ul && U32.eq t 4ul && U32.eq d 8ul) { 0l } else { 1l }
}
