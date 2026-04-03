module MSort.Sequential
#lang-pulse

open Pulse.Lib.Pervasives
module S = FStar.Seq
module SZ = FStar.SizeT
open MSort.SeqLemmas
open MSort.Base


fn rec msort
  (a : array int)
  (lo hi : SZ.t)
  (s : erased (S.seq int))
  requires pts_to_range a (SZ.v lo) (SZ.v hi) (reveal s)
  ensures  pts_to_range a (SZ.v lo) (SZ.v hi) (sort (reveal s))
{
  pts_to_range_prop a;
  if ((hi `SZ.sub` lo) `SZ.lt` 2sz) {
    pts_to_range_prop a;
    singl_is_sorted s;
    ()
  } else {
    let mid : SZ.t = lo `SZ.add` ((hi `SZ.sub` lo) `SZ.div` 2sz);

    pts_to_range_split a (SZ.v lo) (SZ.v mid) (SZ.v hi);

    with s1. assert (pts_to_range a (SZ.v lo) (SZ.v mid) s1);
    with s2. assert (pts_to_range a (SZ.v mid) (SZ.v hi) s2);

    msort a lo mid s1;
    msort a mid hi s2;

    merge_impl a lo mid hi () (sort s1) (sort s2);
  }
}

