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

module MSort.Base
#lang-pulse

open FStar.Ghost
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module S = FStar.Seq
module SZ = FStar.SizeT
open MSort.SeqLemmas

#set-options "--z3rlimit 20"


fn
copy_array
  (src tgt : array int)
  (s_lo t_lo len : SZ.t)
  (#s_src : erased (S.seq int))
  (#s_tgt : erased (S.seq int))
  requires pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src
        ** pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_tgt
  ensures  pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src
        ** pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_src
{
  pts_to_range_prop src;
  pts_to_range_prop tgt;
  let mut i = 0sz;

  while (
    let vi = !i;
    (vi `SZ.lt` len)
  )
    invariant b. exists* vi s_tgt'.
      pts_to i vi **
      pts_to_range src (SZ.v s_lo) (SZ.v s_lo + SZ.v len) s_src **
      pts_to_range tgt (SZ.v t_lo) (SZ.v t_lo + SZ.v len) s_tgt' **
      pure (SZ.v len >= 0 /\
            SZ.v vi <= SZ.v len /\
            s_tgt' == stake (SZ.v vi) s_src `S.append` sdrop (SZ.v vi) s_tgt /\
            SZ.v len == S.length s_src /\
            SZ.v len == S.length s_tgt /\
            (vi `SZ.lt` len == false ==> SZ.v vi == SZ.v len)) **
      pure (b == (SZ.v vi <  SZ.v len)) // can't use <==>, why?
  {
    let ii = !i;

    let v = pts_to_range_index src (s_lo `SZ.add` ii);

    pts_to_range_upd tgt (t_lo `SZ.add` ii) v;
    lem_upd_spliced (SZ.v len) s_src s_tgt (SZ.v ii);

    i := ii `SZ.add` 1sz;
  };

  S.append_empty_r s_src;

  ()
}



fn
merge_impl
  (a : array int) (lo mid hi : SZ.t)
  (_:squash (SZ.v lo <= SZ.v mid /\ SZ.v mid <= SZ.v hi))
  (s1 : erased (S.seq int))
  (s2 : erased (S.seq int))
  requires pts_to_range a (SZ.v lo) (SZ.v mid) s1
        ** pts_to_range a (SZ.v mid) (SZ.v hi) s2
  ensures pts_to_range a (SZ.v lo) (SZ.v hi) (merge s1 s2)
{
  let l1 = mid `SZ.sub` lo;
  let l2 = hi  `SZ.sub` mid;

  pts_to_range_prop a #(SZ.v lo) #(SZ.v mid);
  pts_to_range_prop a #(SZ.v mid) #(SZ.v hi);

  assert (pure (SZ.v l1 == S.length s1));
  assert (pure (SZ.v l2 == S.length s2));

  let sw1 = A.alloc 0 (mid `SZ.sub` lo);
  let sw2 = A.alloc 0 (hi `SZ.sub` mid);

  pts_to_range_intro sw1 1.0R (S.create (SZ.v l1) 0);
  copy_array a sw1 lo 0sz (mid `SZ.sub` lo);
  pts_to_range_elim sw1 1.0R s1;

  pts_to_range_intro sw2 1.0R (S.create (SZ.v l2) 0);
  copy_array a sw2 mid 0sz (hi `SZ.sub` mid);
  pts_to_range_elim sw2 1.0R s2;

  let mut i = 0sz;
  let mut j = 0sz;
  let mut k = 0sz;

  pts_to_range_join a (SZ.v lo) (SZ.v mid) (SZ.v hi);
  
  while (
    let vi = !i;
    let vj = !j;
    (vi `SZ.lt` l1 || vj `SZ.lt` l2)
  )
    invariant b.
      exists* vi vj vk ss.
      pts_to i vi **
      pts_to j vj **
      pts_to k vk **
      pts_to sw1 (reveal s1) **
      pts_to sw2 (reveal s2) **
      pts_to_range a (SZ.v lo) (SZ.v hi) ss **
      pure (SZ.v vi <= SZ.v l1 /\ SZ.v vj <= SZ.v l2 /\ vk == vi `SZ.add` vj /\
            (ss == S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                                (sdrop (SZ.v vk) (S.append s1 s2))) /\
            (b == (vi `SZ.lt` l1 || vj `SZ.lt` l2)))
  {
    let vi = !i;
    let vj = !j;
    let vk = !k;

    if (vi = l1) {
      (* End of l1 *)
      let x = sw2.(vj);

      pts_to_range_upd a (lo `SZ.add` vk) x; //a.(lo + vk) <- x;
      j := vj `SZ.add` 1sz;
      k := vk `SZ.add` 1sz;

      lem_partial_merge_full_l_add (reveal s1) (reveal s2) (S.append (reveal s1) (reveal s2)) (SZ.v vi) (SZ.v vj);
      
      assert
         pts_to_range a (SZ.v lo) (SZ.v hi)
              (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v (vj `SZ.add` 1sz)) (reveal s2)))
                        (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));

    } else if (vj = l2) {
      (* End of l2 *)
      let x = sw1.(vi);
      pts_to_range_upd a (lo `SZ.add` vk) x; //a.(lo + vk) <- x;
      i := vi `SZ.add` 1sz;
      k := vk `SZ.add` 1sz;

      lem_partial_merge_full_r_add (reveal s1) (reveal s2) (S.append (reveal s1) (reveal s2)) (SZ.v vi) (SZ.v vj);

      assert
         pts_to_range a (SZ.v lo) (SZ.v hi)
              (S.append (merge (stake (SZ.v (vi `SZ.add` 1sz)) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                        (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));
    } else {
      let x = sw1.(vi);
      let y = sw2.(vj);
      if (x <= y) {
        pts_to_range_upd a (lo `SZ.add` vk) x; //a.(lo + vk) <- x;
        i := vi `SZ.add` 1sz;
        k := vk `SZ.add` 1sz;
        
        lem_partial_merge_left_add (reveal s1) (reveal s2) (S.append (reveal s1) (reveal s2)) (SZ.v vi) (SZ.v vj);

        assert
          pts_to_range a (SZ.v lo) (SZ.v hi)
                (S.append (merge (stake (SZ.v (vi `SZ.add` 1sz)) (reveal s1)) (stake (SZ.v vj) (reveal s2)))
                          (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));
      } else {
        pts_to_range_upd a (lo `SZ.add` vk) y; //a.(lo + vk) <- y;
        j := vj `SZ.add` 1sz;
        k := vk `SZ.add` 1sz;

        lem_partial_merge_right_add (reveal s1) (reveal s2) (S.append (reveal s1) (reveal s2)) (SZ.v vi) (SZ.v vj);

        assert
          pts_to_range a (SZ.v lo) (SZ.v hi)
                (S.append (merge (stake (SZ.v vi) (reveal s1)) (stake (SZ.v (vj `SZ.add` 1sz)) (reveal s2)))
                          (sdrop (SZ.v (vk `SZ.add` 1sz)) (S.append s1 s2)));
      };
    }
  };

  A.free sw1;
  A.free sw2;
}

