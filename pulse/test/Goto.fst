module Goto
open Pulse
open Pulse.Lib.WithPure
#lang-pulse

fn test1 (r: ref int)
    preserves live r
{
  {
    goto fail;
    label fail:
  }
}

fn find_zero (a: array int) (sz: SizeT.t)
  preserves pts_to a #'r 'va
  requires with_pure (SizeT.v sz <= Seq.length 'va)
  returns i: SizeT.t
  ensures pure (SizeT.v i <= SizeT.v sz /\
    (forall (j: nat). j < SizeT.v i ==> Seq.index 'va j <> 0))
  ensures pure (SizeT.v i < SizeT.v sz ==> Seq.index 'va (SizeT.v i) == 0)
{{
  let mut i: SizeT.t = 0sz;
  while (!i `SizeT.lt` sz)
    invariant live i
    invariant pure (SizeT.v !i <= SizeT.v sz /\
      (forall (j: nat). j < SizeT.v (!i) ==> Seq.index 'va j <> 0))
  {
    if (a.(!i) = 0) {
      goto return (!i);
    } else {
      i := !i `SizeT.add` 1sz;
    }
  };
  !i
  label return:
}}