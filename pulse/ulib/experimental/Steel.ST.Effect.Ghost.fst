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

module Steel.ST.Effect.Ghost
friend Steel.ST.Effect.AtomicAndGhost
friend Steel.Effect.Atomic
open Steel.Memory
module T = FStar.Tactics
module SEA = Steel.Effect.Atomic


/// Any Steel ghost computation can always be lifted to an atomic computation if needed.
/// Note that because SteelGhost is marked as erasble, the F* typechecker will throw an error
/// if this lift is applied to a ghost computation with an informative return value
let lift_ghost_atomic
    (a:Type)
    (opened:inames)
    (#framed:eqtype_as_type bool)
    (#[@@@ framing_implicit] pre:pre_t)
    (#[@@@ framing_implicit] post:post_t a)
    (#[@@@ framing_implicit] req:Type0)
    (#[@@@ framing_implicit] ens:a -> Type0)
    (f:STAG.repr a framed opened Unobservable pre post req ens)
  : STAG.repr a framed opened Unobservable pre post req ens
  = f

let as_atomic_action_ghost (#a:Type u#a)
                           (#opened_invariants:inames)
                           (#fp:slprop)
                           (#fp': a -> slprop)
                           (f:action_except a opened_invariants fp fp')
  : STGhostT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))
  = let ff = SEA.reify_steel_ghost_comp (fun _ -> SEA.as_atomic_action_ghost f) in
    STGhostBase?.reflect ff


let extract_fact0 (#opened:inames)
                  (p:vprop)
                  (fact:prop)
                  (l:(m:mem) -> Lemma
                      (requires interp (hp_of p) m)
                      (ensures fact))
  : STAG.repr unit false opened Unobservable p (fun _ -> p) True (fun _ -> fact)
  = fun frame ->
      let m0:full_mem = NMSTTotal.get () in
      Classical.forall_intro_3 reveal_mk_rmem;
      let h0 = mk_rmem p (core_mem m0) in
      l (core_mem m0)

let extract_fact (#opened:inames)
                 (p:vprop)
                 (fact:prop)
                 (l:(m:mem) -> Lemma
                                (requires interp (hp_of p) m)
                                (ensures fact))
  : STGhost unit opened p (fun _ -> p) True (fun _ -> fact)
  = STGhostBase?.reflect (extract_fact0 p fact l)

let admit_ _ = STGhostF?.reflect (fun _ -> NMSTTotal.nmst_tot_admit ())
