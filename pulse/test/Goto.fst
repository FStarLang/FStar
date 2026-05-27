module Goto
open Pulse
open Pulse.Lib.WithPure
#lang-pulse

fn test1 (r: ref Int32.t)
    preserves live r
{
  {
    r := 42l;
    let mut x : UInt32.t;
    x := 1ul;
    goto fail;
  }
  label fail:
  // x not in scope for cleanup
}

fn find_zero (a: array Int32.t) (sz: SizeT.t)
  preserves pts_to a #'r 'va
  requires with_pure (SizeT.v sz <= Seq.length 'va)
  returns i: SizeT.t
  ensures pure (SizeT.v i <= SizeT.v sz /\
    (forall (j: nat). j < SizeT.v i ==> Seq.index 'va j <> 0l))
  ensures pure (SizeT.v i < SizeT.v sz ==> Seq.index 'va (SizeT.v i) == 0l)
{
  let mut i: SizeT.t = 0sz;
  while (!i `SizeT.lt` sz)
    invariant live i
    invariant pure (SizeT.v !i <= SizeT.v sz /\
      (forall (j: nat). j < SizeT.v (!i) ==> Seq.index 'va j <> 0l))
  {
    if (a.(!i) = 0l) {
      return !i;
    };

    i := !i `SizeT.add` 1sz;
  };
  !i
}

//labels with impure specs in ensures
fn test2_alt (r: ref Int32.t)
    preserves live r
    ensures pure (!r == 17l \/ !r == 42l)
{
  {
    if (!r = 67l) { r := 42l; return; };
    goto fail;
  }
  ensures live r ** pure (!r <> 67l)
  label fail:;
  r := 17l;
}