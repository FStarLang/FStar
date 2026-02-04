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

module Quicksort.Sequential
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array

open Quicksort.Base


fn rec quicksort (a: A.array int) (lo: nat) (hi:(hi:nat{lo <= hi})) (lb rb: erased int) (#s0: Ghost.erased (Seq.seq int))
  requires A.pts_to_range a lo hi s0
  requires pure (pure_pre_quicksort a lo hi lb rb s0)
  ensures exists* s. (A.pts_to_range a lo hi s ** pure (pure_post_quicksort a lo hi lb rb s0 s))
{
  if (lo < hi - 1)
  {
    let r = partition_wrapper a lo hi lb rb;
    let pivot = r._3;
    with s1. assert (A.pts_to_range a lo r._1 s1);
    with s2. assert (A.pts_to_range a r._1 r._2 s2);
    with s3. assert (A.pts_to_range a r._2 hi s3);

    quicksort a lo r._1 lb pivot;
    quicksort a r._2 hi pivot rb;
    
    with s1'. assert (A.pts_to_range a lo r._1 s1');
    with s3'. assert (A.pts_to_range a r._2 hi s3');
    
    let _ = append_permutations_3_squash s1 s2 s3 s1' s3' ();

    quicksort_proof a lo r._1 r._2 hi lb rb pivot #s0 s1' s2 s3';
  }
}

