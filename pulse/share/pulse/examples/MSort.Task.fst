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

module MSort.Task
#lang-pulse

open Pulse.Lib.Pervasives
module S = FStar.Seq
module SZ = FStar.SizeT
open MSort.SeqLemmas
open MSort.Base
open NuPool


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

    let h = spawn p #(f /. 2.0R) (fun () -> t_msort_par p (f /. 2.0R) a lo mid s1);
    t_msort_par p (f /. 2.0R) a mid hi s2;
    await h;

    gather_alive p f;

    merge_impl a lo mid hi () (sort s1) (sort s2);
  }
}



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
  t_msort_par p 1.0R a lo hi s;
  teardown_pool p;
  drop_ (pool_done p);
}

