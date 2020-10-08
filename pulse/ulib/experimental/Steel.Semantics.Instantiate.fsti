(*
   Copyright 2020 Microsoft Research

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

module Steel.Semantics.Instantiate

module S = Steel.Semantics.Hoare.MST
open Steel.Memory

let state0 (uses:inames) : S.st0 =
  {
    S.mem = mem;
    S.core = core_mem;
    S.full_mem_pred = full_mem_pred;
    S.locks_preorder = mem_evolves;
    S.hprop = slprop;
    S.locks_invariant = locks_invariant uses;

    S.disjoint = disjoint;
    S.join = join;

    S.interp = interp;

    S.emp = emp;
    S.star = star;

    S.equals = equiv
  }

val state_obeys_st_laws (uses:inames)
  : Lemma (S.st_laws (state0 uses))

let state_uses (uses:inames) : S.st = state_obeys_st_laws uses; state0 uses

let state : S.st = state_uses Set.empty

val state_correspondence (inames:inames)
  : Lemma
    (let s = state_uses inames in
     s.S.hprop == slprop /\
     s.S.mem == mem /\
     s.S.interp == interp /\
     s.S.star == star /\
     s.S.locks_invariant == locks_invariant inames /\
     (forall (p q frame:slprop)
        (m0:mem{interp (p `star` frame `star` locks_invariant inames m0) m0})
        (m1:mem{interp (q `star` frame `star` locks_invariant inames m1) m1}).
       (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)) ==> 
       S.post_preserves_frame #s q frame m0 m1))
