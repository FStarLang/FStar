module MSortPar

open FStar.Ghost
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module S = FStar.Seq
module SZ = FStar.SizeT

open MSort
open MSort.SeqLemmas
open TaskPool
open Pulse.Lib.Par.Pledge

```pulse
fn
rec
t_msort_par
  (p : pool)
  (f : perm)
  (a : array int)
  (lo hi : SZ.t)
  (s : erased (S.seq int))
  requires pool_alive #f p ** pts_to_range a (SZ.v lo) (SZ.v hi) (reveal s)
  ensures  pool_alive #f p ** pts_to_range a (SZ.v lo) (SZ.v hi) (sort (reveal s))
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
    
    share_alive p f;

    let h = spawn p #(half_perm f) (fun () -> t_msort_par p (half_perm f) a lo mid s1);
    t_msort_par p (half_perm f) a mid hi s2;
    join h;
    
    gather_alive p f;

    merge_impl a lo mid hi () (sort s1) (sort s2);
  }
}
```
