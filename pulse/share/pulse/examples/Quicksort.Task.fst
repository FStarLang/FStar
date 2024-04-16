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

module QuickSort.Task

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

open Pulse.Lib.InvList

module T = Pulse.Lib.Task
open Quicksort.Base
open Pulse.Lib.Pledge

let quicksort_post a lo hi s0 lb rb : vprop =
  exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))

```pulse
fn rec t_quicksort
  (p : T.pool)
  (#f : perm)
  (a : A.array int)
  (lo : nat) (hi : (hi:nat{lo <= hi}))
  (#lb #rb : erased int)
  (#s0 : erased (Seq.seq int))
  requires
    T.pool_alive #f p **
    A.pts_to_range a lo hi s0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures 
    pledge emp_inames (T.pool_done p) (
      T.pool_alive #f p **
      quicksort_post a lo hi s0 lb rb
    )
{
  if (lo < hi - 1)
  {
    let r = partition_wrapper a lo hi lb rb;
    let pivot = r._3;
    with s1. assert (A.pts_to_range a lo r._1 s1);
    with s2. assert (A.pts_to_range a r._1 r._2 s2);
    with s3. assert (A.pts_to_range a r._2 hi s3);

    T.share_alive p f;

    T.spawn_ p #(half_perm f) (fun () -> t_quicksort p #(half_perm f) a lo r._1 #lb #pivot);
    t_quicksort p #(half_perm f) a r._2 hi #pivot #rb;
    
    return_pledge (T.pool_done p) (A.pts_to_range a r._1 r._2 s2);
    squash_pledge _ _ _;
    join_pledge _ _;
    join_pledge _ _;

    ghost fn rewrite_pf ()
      // NB: These two vprops have to be in exactly this shape, as the Pulse checker
      // will not commute or in anyway modify each side of the pledge. The function
      // above must also be in this exact shape. To obtain the shape, I just manually looked
      // at the context. Automation should likely help here.
      requires
        (T.pool_alive #(half_perm f) p ** quicksort_post a lo r._1 s1 lb pivot) **
        A.pts_to_range a r._1 r._2 s2 **
        (T.pool_alive #(half_perm f) p ** quicksort_post a r._2 hi s3 pivot rb)
      ensures
        T.pool_alive #f p **
        quicksort_post a lo hi s0 lb rb
    {
      (* Functional correctness *)
      unfold quicksort_post;
      unfold quicksort_post;
      quicksort_proof a lo r._1 r._2 hi lb rb pivot #s0 s1 s2 s3;
      fold (quicksort_post a lo hi s0 lb rb);

      (* Permission accounting *)
      T.gather_alive p f;
    };
    rewrite_pledge _ _ rewrite_pf;

    ()
  } else {
    return_pledge (T.pool_done p) (
      T.pool_alive #f p **
      (exists* s. A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
    );
  }
}
```

assume val split_pledge (#is:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_atomic (pi:invlist_elem { not (mem_inv is (snd pi)) })
               is
               (pledge is f (v1 ** v2))
               (fun pi -> pledge (Set.add (iname_of (snd pi)) is) f v1 ** pledge (Set.add (iname_of (snd pi)) is) f v2)

```pulse
fn rec quicksort
  (nthr : pos)
  (a : A.array int)
  (lo : nat) (hi : (hi:nat{lo <= hi}))
  (#lb #rb : erased int)
  (#s0 : erased (Seq.seq int))
  requires
    A.pts_to_range a lo hi s0 **
    pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures
    quicksort_post a lo hi s0 lb rb
{
  let p = T.setup_pool nthr;

  T.share_alive p _;

  t_quicksort p a lo hi #lb #rb;

  let i = split_pledge _ _;
  
  assume_ (pure (comp_perm (half_perm full_perm) == half_perm full_perm)); // F* limitation, real arith

  admit ();
  T.teardown_pool' p _;
  redeem_pledge _ _ _;
  drop_ (T.pool_done p)
}
```
