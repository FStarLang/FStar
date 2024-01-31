(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module QuickSort.TaskParallel
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
open Pulse.Lib.InvList

module T = TaskPool
open QuickSortParallel
open Pulse.Lib.Par.Pledge

let quicksort_post a lo hi s0 lb rb : vprop =
  exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))

```pulse
ghost
fn join_alive_pledge (p:T.pool) (f:perm)
  requires pledge is (T.pool_done p) (T.pool_alive #(half_perm f) p)
        ** pledge is (T.pool_done p) (T.pool_alive #(half_perm f) p)
  ensures pledge is (T.pool_done p) (T.pool_alive #f p)
{
  join_pledge #is #(T.pool_done p) (T.pool_alive #(half_perm f) p) (T.pool_alive #(half_perm f) p);

  ghost fn
    rewrite_pf
      (_:unit)
      requires
        invlist_v is **
        (T.pool_alive #(half_perm f) p ** T.pool_alive #(half_perm f) p)
      ensures
        invlist_v is **
        (T.pool_alive #f p)
    {
      T.gather_alive p f;
    };
  
  rewrite_pledge #is #(T.pool_done p)
    (T.pool_alive #(half_perm f) p ** T.pool_alive #(half_perm f) p)
    (T.pool_alive #f p)
    rewrite_pf;
}
```

(* NOTE: This is still a sketch as it is not spawning any of the sub tasks, but instead
just calling sequentially. Already, however, pledge arithmetic is quite a big part
of this proof. Spawning a subtask will require the use of split for permission
accounting and complicate things further due to the extra invariant, unless we use
the simple interface instead. *)
```pulse
fn rec t_quicksort
  (p : T.pool)
  (f : perm)
  (a: A.array int)
  (lo: nat) (hi:(hi:int{-1 <= hi - 1 /\ lo <= hi}))
  (lb rb: int)
  (#s0: Ghost.erased (Seq.seq int))
  requires
    T.pool_alive #f p **
    A.pts_to_range a lo hi s0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures 
    pledge [] (T.pool_done p) (T.pool_alive #f p) **
    pledge [] (T.pool_done p) (quicksort_post a lo hi s0 lb rb)
{
  if (lo < hi - 1)
  {
    let r = partition_wrapper a lo hi lb rb;
    let pivot = r._3;
    with s1. assert (A.pts_to_range a lo r._1 s1);
    with s2. assert (A.pts_to_range a r._1 r._2 s2);
    with s3. assert (A.pts_to_range a r._2 hi s3);

    T.share_alive p f;

    t_quicksort p (half_perm f) a lo r._1 lb pivot;
    t_quicksort p (half_perm f) a r._2 hi pivot rb;
    
    (* pledge arith *)
    return_pledge [] (T.pool_done p) (A.pts_to_range a r._1 r._2 s2);
    join_pledge #[] #(T.pool_done p)
      (A.pts_to_range a r._1 r._2 s2)
      (quicksort_post a lo r._1 s1 lb pivot);
    join_pledge #[] #(T.pool_done p)
      (A.pts_to_range a r._1 r._2 s2 ** quicksort_post a lo r._1 s1 lb pivot)
      (quicksort_post a r._2 hi s3 pivot rb);
      
    ghost fn
    rewrite_pf
      (_:unit)
      requires
        emp ** // invs
        (A.pts_to_range a r._1 r._2 s2 ** quicksort_post a lo r._1 s1 lb pivot ** quicksort_post a r._2 hi s3 pivot rb)
      ensures
        emp ** // invs
        quicksort_post a lo hi s0 lb rb
    {
      unfold quicksort_post;
      unfold quicksort_post;
      quicksort_proof a lo r._1 r._2 hi lb rb pivot #s0 s1 s2 s3;
      fold (quicksort_post a lo hi s0 lb rb);
    };
    rewrite_pledge #[] #(T.pool_done p)
        (A.pts_to_range a r._1 r._2 s2 ** quicksort_post a lo r._1 s1 lb pivot ** quicksort_post a r._2 hi s3 pivot rb)
        (quicksort_post a lo hi s0 lb rb)
        rewrite_pf;

    join_alive_pledge p f;

    ()
  } else {
    return_pledge [] (T.pool_done p)
      (exists* s. A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s));
    return_pledge [] (T.pool_done p)
      (T.pool_alive #f p);
  }
}
```
