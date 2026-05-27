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

module Quicksort.Task
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array

module T = Pulse.Lib.Task
open Quicksort.Base
open Pulse.Lib.Pledge

let quicksort_post a lo hi s0 lb rb : slprop =
  exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))

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
    let p31, p32, pivot = partition_wrapper a lo hi lb rb;
    with s1. assert (A.pts_to_range a lo p31 s1);
    with s2. assert (A.pts_to_range a p31 p32 s2);
    with s3. assert (A.pts_to_range a p32 hi s3);

    T.share_alive p f;

    T.spawn_ p #(f /. 2.0R) (fun () -> t_quicksort p #(f /. 2.0R) a lo p31 #lb #pivot #s1);
    t_quicksort p #(f /. 2.0R) a p32 hi #pivot #rb;

    return_pledge (T.pool_done p) (A.pts_to_range a p31 p32 s2) #_;
    squash_pledge _ _ _;
    (* disambiguating makes this pretty inconvenient now, but it is robust at least... *)
    join_pledge (T.pool_alive #(f /. 2.0R) p ** quicksort_post a lo p31 s1 lb pivot) (A.pts_to_range a p31 p32 s2);
    join_pledge _ (T.pool_alive #(f /. 2.0R) p ** quicksort_post a p32 hi s3 pivot rb);

      // NB: These two slprops have to be in exactly this shape, as the Pulse checker
      // will not commute or in anyway modify each side of the pledge. The function
      // above must also be in this exact shape. To obtain the shape, I just manually looked
      // at the context. Automation should likely help here.
    rewrite_pledge
        (((T.pool_alive #(f /. 2.0R) p ** quicksort_post a lo p31 s1 lb pivot) **
            A.pts_to_range a p31 p32 s2) **
          (T.pool_alive #(f /. 2.0R) p ** quicksort_post a p32 hi s3 pivot rb))
        (T.pool_alive #f p **
          quicksort_post a lo hi s0 lb rb)
        #emp_inames
      fn _
    {
      (* Functional correctness *)
      unfold (quicksort_post a lo p31 s1 lb pivot);
      unfold quicksort_post;
      quicksort_proof a lo p31 p32 hi lb rb pivot #s0 s1 s2 s3;
      fold (quicksort_post a lo hi s0 lb rb);

      (* Permission accounting *)
      T.gather_alive p f;
    };

    ()
  } else {
    fold (quicksort_post a lo hi s0 lb rb);
    return_pledge (T.pool_done p) (
      T.pool_alive #f p **
      quicksort_post a lo hi s0 lb rb
    ) #_;
  }
}

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

  // let i = split_pledge _ _;

  T.await_pool p (T.pool_alive #(1.0R /. 2.0R) p ** _);

  T.gather_alive p _;

  T.teardown_pool p;
  // redeem_pledge _ _ _;
  drop_ (T.pool_done p)
}

