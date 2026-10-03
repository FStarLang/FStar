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
  (* A comment around a call result, and one nested inside another. *)
  let t = comment_gen "outer before"
            (comment_gen "inner before" (count_to 4sz) "inner after")
            "outer after";
  (* Nothing reads this one.  The comment survives anyway. *)
  let unused = comment_gen "kept" 0ul "even unread";
  let d = twice t;
  if (U32.eq t 4ul && U32.eq d 8ul) { 0l } else { 1l }
}
