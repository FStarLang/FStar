module Break
open Pulse
open Pulse.Lib.WithPure
#lang-pulse

fn simple_break ()
{
  let mut k = true;
  while (!k)
    invariant live k
    break requires true
  {
    break;
  }
}

fn find_zero_with_break (a: array Int32.t) (sz: SizeT.t)
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
    break requires (SizeT.v !i < SizeT.v sz /\ a.(!i) = 0l)
  {
    if (a.(!i) = 0l) {
      break;
    };

    i := !i `SizeT.add` 1sz;
  };
  !i
}
