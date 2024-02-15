module MSort.Task

open Pulse.Lib.Pervasives
module S = FStar.Seq
module SZ = FStar.SizeT
open MSort.SeqLemmas
open MSort.Base
open Pulse.Lib.Task

```pulse
fn rec t_msort_par
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

```pulse
fn rec msort
  (nthr : pos)
  (a : array int)
  (lo hi : SZ.t)
  (s : erased (S.seq int))
  requires pts_to_range a (SZ.v lo) (SZ.v hi) (reveal s)
  ensures  pts_to_range a (SZ.v lo) (SZ.v hi) (sort (reveal s))
{
  // No need for pledge reasoning here as t_msort_par is synchronous, even
  // if it parallelizes internally.
  let p = setup_pool nthr;
  t_msort_par p full_perm a lo hi s;
  teardown_pool p;
  drop_ (pool_done p);
}
```
